#!/usr/bin/gosh
;;; Written by Rui Ueyama (rui314@gmail.com).  Public domain.
(use srfi-1)
(use srfi-13)
(use gauche.parameter)
(use util.match)

(debug-print-width #f)

;;;
;;; This is an experimental implementation of recursive-descending parser combined with
;;; breath-first search.
;;;
;;; The basic idea of this came from Russ Cox's RE2 algorithm.  He revived an algorithm
;;; called Thompson NFA for regexp matching, which traverses all possible NFA states
;;; simultaneously in order to avoid backtracking.  He claimed Thompson NFA outperformed
;;; backtracking regexp implementation.
;;;
;;; Two lists are used to execute Thompson NFA; one is CLIST (current list) that stores
;;; all state the state machine is at, and NLIST (next list) stores all states the state
;;; machine will be at next.  At first, CLIST contains only one state, "start" state.  The
;;; simulator reads a character from an input port, search all matching states from CLIST,
;;; and add their next states to NLIST.  Note that because one state can have up to two
;;; next states, NLIST can become larger than CLIST.  Once CLIST is depleted, contents of
;;; NLIST are moved to CLIST, NLIST is initialized with the empty list, and the next cycle
;;; starts.  The simulator stops when it finds a node with "accept" flag, which indicate
;;; match suceeded.
;;;
;;; For more info about RE2, see http://swtch.com/~rsc/regexp/regexp1.html.
;;;
;;; This experimental parser similar to RE2, but it is differerent in the sense that it is
;;; trying to be more generic.  The only thing we can do with a regexp is capturing
;;; submatches.  What if we can combine the idea of Thompson NFA with flexibility of
;;; recursive-descending parser?  I think such a combination is feasible.  Every time a
;;; function reads a character, it should push a function to parse further to NLIST,
;;; instead of calling the function directly.  This makes the parser to do breath-first
;;; search, eliminating the need to backtrack.  I'll write more code to see how I can do
;;; with this idea. [ruiu]
;;;

;;;
;;; Represents NFA node.  Pattern may have the following value:
;;; 
;;;   Charset - indicates the current input must match with the charset.
;;;
;;;   #f - both 'next' and 'next1' have next states and NFA simulator must execute both
;;;   state at the next stage.
;;;
;;;   :exec - 'next' and 'next1' have no values.  NFA simulator must execute 'accumfn' to
;;;   generate a semantic value.
;;;
;;;   :fail - this state matches always fails.
;;;
;;;   :eof - this state matches EOF.
;;;
(define-class <state> ()
  ((pattern :init-keyword :pattern :init-value #f)
   (next    :init-keyword :next    :init-value #f)
   (next1   :init-keyword :next1   :init-value #f)
   (accumfn :init-keyword :accumfn :init-value cons)
   (accept  :init-keyword :accept  :init-value #f)))
   
(define-method write-object ((o <state>) out)
  (format out "#<state ~s ~s ~s ~s>"
          (ref o 'pattern)
          (ref o 'accept)
          (ref o 'next1)
          (ref o 'next)))

(define (set!-tails tails next)
  (for-each (lambda (tail)
              (set! (ref tail 'next) next))
            tails))

;;;
;;; Reads a pattern and constructs NFA.  Patterns are simliar to regular expression, while
;;; the notation is different.  Here's a list of examples written both in regexp and the
;;; pattern.
;;;
;;;    /a/       #\a
;;;    /X|Y.../  (:or X Y ...)
;;;    /[abc]/   #[abc]
;;;    /abc/     "abc"
;;;    /$/       :eof
;;;    /X*/      (:rep X)
;;;    /XY.../   (:seq X Y ...)
;;;
(define (bfs pattern)
  (define (compile pat)
    (match pat
      ((? char? _)
       (let1 state (make <state> :pattern (char-set pat))
         (list state state)))
      ((? char-set? _)
       (let1 state (make <state> :pattern pat)
         (list state state)))
      ((? string? _)
       (let1 head (make <state> :pattern :exec :accumfn (lambda (acc) (parser-push! acc) '()))
         (receive (head1 tails) (car+cdr (compile (cons :seq (string->list pat))))
           (let1 tail (make <state> :pattern :exec :accumfn (lambda (acc) (cons (reverse-list->string acc) (parser-pop!))))
             (set! (ref head 'next) head1)
             (set!-tails tails tail)
             (list head tail)))))
      (((or :seq :rep))
       (let1 state (make <state>)
         (list state state)))
      ((:seq x . rest)
       (receive (head tails) (car+cdr (compile x))
         (receive (head1 tails1) (car+cdr (compile (cons :seq rest)))
           (set!-tails tails head1)
           (cons head tails1))))
      ((:rep . rest)
       (let1 head (make <state>)
         (receive (head1 tails) (car+cdr (compile (cons :seq rest)))
           (set! (ref head 'next1) head1)
           (set!-tails tails head)
           (list head head))))
      ((:or)
       (let1 state (make <state> :pattern :fail)
         (list state state)))
      ((:or x . y)
       (let1 head (make <state>)
         (receive (head1 tails1) (car+cdr (compile x))
           (receive (head2 tails2) (car+cdr (compile (cons :or y)))
             (set! (ref head 'next) head1)
             (set! (ref head 'next1) head2)
             (cons head (append tails1 tails2))))))
      (:eof
       (let1 state (make <state> :pattern :eof)
         (list state state)))))
  (receive (head tails) (car+cdr (compile pattern))
    (let1 end (make <state> :accept #t)
      (set!-tails tails end)
      head)))

;;;
;;; Helper functions to construct semantic values.
;;;
(define parser-stack (make-parameter '()))

(define (parser-push! val)
  (parser-stack (cons val (parser-stack))))

(define (parser-pop!)
  (begin0 (car (parser-stack))
          (parser-stack (cdr (parser-stack)))))

;;;
;;; Parser.  Clist is an alist of ((<state> . <parsing-result>) ...), where
;;; <parsing-result> is a semantic value being constructed.
;;;
(define (parse* start-state input)
  (define (main)
    (let loop ((clist (list (list start-state))))
      (let1 c (read-char input)
        (let loop1 ((clist1 clist)
                    (nlist '()))
          (define (redo state)
            (loop1 (if (ref state 'next1)
                     (cons* (cons (ref state 'next)  (cdar clist1))
                            (cons (ref state 'next1) (cdar clist1))
                            (cdr clist1))
                     (acons (ref state 'next) (cdar clist1) (cdr clist1)))
                   nlist))
          (define (next state)
            (loop1 (cdr clist1)
                   (if (ref state 'next1)
                     (cons* (cons (ref state 'next)  ((ref state 'accumfn) c (cdar clist1)))
                            (cons (ref state 'next1) ((ref state 'accumfn) c (cdar clist1)))
                            nlist)
                     (acons (ref state 'next)
                            ((ref state 'accumfn) c (cdar clist1))
                            nlist))))
          (define (fail)
            (loop1 (cdr clist1) nlist))
          (cond ((and (null? clist1) (null? nlist))
                 (error #`"match failed at ,c"))
                ((null? clist1)
                 (loop nlist))
                (else
                 (let* ((state (caar clist1))
                        (pattern (ref state 'pattern)))
                   (cond ((ref state 'accept)
                          (cdar clist1))
                         ((eq? pattern :exec)
                          (loop1 (acons (ref state 'next)
                                        ((ref state 'accumfn) (cdar clist1))
                                        (cdr clist1))
                                 nlist))
                         ((eq? pattern :fail)
                          (fail))
                         ((eq? pattern :eof)
                          (if (eof-object? c)
                            (redo state)
                            (fail)))
                         ((eq? pattern #f)
                          (loop1 (if (ref state 'next1)
                                   (cons* (cons (ref state 'next)  (cdar clist1))
                                          (cons (ref state 'next1) (cdar clist1))
                                          (cdr clist1))
                                   (cons (cons (ref state 'next) (cdar clist1))
                                         (cdr clist1)))
                                 nlist))
                         ((and (not (eof-object? c)) (char-set-contains? pattern c))
                          (next state))
                         ((eof-object? c)
                          (error "premature end of input"))
                         (else
                          (fail))))))))))
  (parameterize ((parser-stack '()))
    (main)))

;;;
;;; Entry point.
;;;
(define (parse expr str)
  (parse* (bfs expr) (open-input-string str)))

;;;
;;; Examples.
;;;
(write (parse '(:seq (:rep (:or "ab" "XY")) :eof) "abXYab"))
(newline)
(exit)
#?=(parse* #?=(bfs '(:seq (:rep "ab") :eof)) (open-input-string "ababab"))
(exit)
#?=(parse* (bfs '(:seq #\a (:or (:rep #\b #\c) #\j) #\d)) (open-input-string "abcbcd"))
