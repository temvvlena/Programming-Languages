#lang scheme

(require (lib "tls.ss" "Luther"))


;;;;;;;;
;;;;;;;; Procedure (rightmost lis)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Finds the rightmost atom in a list
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis is an arbitrarily-complex list
;;;;;;;;
;;;;;;;; Returns:
;;;;;;;;     Returns the rightmost atom in lis, if lis contains any atoms;  otherwise,
;;;;;;;;         returns ()
;;;;;;;;
;;;;;;;; Worst-case asymptotic run time:
;;;;;;;;     O(# of cons cells in lis)
;;;;;;;;
;;;;;;;; Notes:
;;;;;;;;     Carefully orders the conditional-expression clauses in order to examine as
;;;;;;;;         little as possible of the structure of lis by exploring the cdr of lis
;;;;;;;;         before exploring a non-atomic car of lis
;;;;;;;;     Does *not* use the right-end proceudes rac or rdc, since this would lead to
;;;;;;;;         needlessly-large asymptotic run-times
;;;;;;;;     Uses a let-expression to avoid repeated computation, since this would lead to
;;;;;;;;         needlessly-large asymptotic run-times
;;;;;;;;


(define rightmost
  (lambda (lis)
    (if
     (null? lis)
     '()
     (let
         ((rightmost-cdr-lis (rightmost (cdr lis))))
       (cond
         ((not (null? rightmost-cdr-lis)) rightmost-cdr-lis)
         ((atom? (car lis)) (car lis))
         (else (rightmost (car lis))))))))


;;;;;;;;
;;;;;;;; Procedure (destructure lis+)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Produces a representation having minimal internal structure
;;;;;;;;     of an arbitrarily-complex list 
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis+ is an arbitrarily-complex list
;;;;;;;;
;;;;;;;; Returns
;;;;;;;;     Returns a list that looks like the list lis+ would look if
;;;;;;;;     one replaced all the left parentheses with the list (lp) and all
;;;;;;;;     the right parentheses with the list (rp)
;;;;;;;;
;;;;;;;; Worst-case asymptotic run time:
;;;;;;;;     O(1 + (# of cons cells making up lis+)^2)
;;;;;;;;         (which requires a bit of analysis to come up with)
;;;;;;;;


(define destructure
  (lambda (lis+)
    (cond
      ((null? lis+) '((lp) (rp)))
      ((atom? (car lis+)) (cons '(lp) (cons (car lis+) (cdr (destructure (cdr lis+))))))
      (else (cons '(lp) (append (destructure (car lis+)) (cdr (destructure (cdr lis+)))))))))


;;;;;;;;
;;;;;;;; Procedure (deepest-atom lis+)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Finds the deepest, leftmost atom in an abrbitrarily-complex list
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis+ is an arbitrarily-complex list
;;;;;;;;
;;;;;;;; Returns:
;;;;;;;;     If lis+ contains any atoms, returns the deepest atom in lis+,
;;;;;;;;         where "depth" is defined as the number of layers of
;;;;;;;;         parentheses an atom is enclosed in.  (If there are two
;;;;;;;;         or more atoms at the same maximal depth, the leftmost
;;;;;;;;         one with respect to the front of the list is returned.
;;;;;;;;     If lis+ contains no atoms, returns ().
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + (# of cons cells in lis+))
;;;;;;;;


(define deepest-atom
  (lambda (lis+)
    (car (deepest-atom-tagged-with-depth lis+ 0))))


;;;;
;;;; Procedure (deepest-atom-tagged-with-depth lis* depth-of-lis*)
;;;;
;;;; Purpose:
;;;;     Returns a pair containing the deepest, leftmost atom in lis*
;;;;     together with the depth at which that atom occurred
;;;;
;;;; Pre-conditions:
;;;;     lis* is an arbitrary S-expression
;;;;     depth-of-lis* is a non-negative integer giving the depth
;;;;         of lis* within its enclosing list, if any
;;;;
;;;; Returns:
;;;;     If lis* contains an atom, returns a pair containing the
;;;;         deepest atom in x (where "depth" is defined as the
;;;;         number of layers of parentheses an item is enclosed
;;;;         in) together with the value
;;;;
;;;;             depth + (depth at which that atom occurred in lis*)
;;;;
;;;;         If there are two or more atoms at the same maximal depth,
;;;;         the leftmost one with respect to the front of the list
;;;;         is returned.
;;;;     If there are no atoms in lis*, returns (() -1)
;;;;
;;;; Worst-case asymptotic run-time:
;;;;     O(1 + (# of cons cells is lis*))
;;;;


(define deepest-atom-tagged-with-depth
  (lambda (lis* depth-of-lis*)
    (cond
      ((null? lis*) '(() -1))
      ((atom? lis*) (list lis* depth-of-lis*))
      (else
       (let
           ((car-result (deepest-atom-tagged-with-depth (car lis*) (+ 1 depth-of-lis*)))
            (cdr-result (deepest-atom-tagged-with-depth (cdr lis*) depth-of-lis*)))
         (if
          (>= (cadr car-result) (cadr cdr-result))
          car-result
          cdr-result))))))


;;;;;;;;
;;;;;;;; Procedure (sequence-atoms lis+ initial increment)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Tags each atom in an arbitrarily-complex list with a sequence-indicating
;;;;;;;;     number
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis+ is an arbitrarily-complex list
;;;;;;;;     initial is a number
;;;;;;;;     increment is a number
;;;;;;;;
;;;;;;;; Reutrns:
;;;;;;;;     A list that looks like lis+ with each atom atm replaced by
;;;;;;;;
;;;;;;;;         (: j atm)
;;;;;;;;
;;;;;;;;          where j is a sequence number;  if atm is the k-th atom
;;;;;;;;         (k >= 0) from the left of lis+, j = initial + (k * increment)
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + (number of cons-cells in lis+))
;;;;;;;;


(define sequence-atoms
  (lambda (lis+ initial increment)
    (car (sequence-atoms-aux lis+ initial increment))))


;;;;
;;;; Procedure (sequence-atoms-aux lis+ initial increment)
;;;;
;;;; Purpose:
;;;;     Tags each atom in an arbitrarily-complex list with a sequence-indicating
;;;;     number
;;;;
;;;; Pre:
;;;;     lis+ is an arbitrarily-complex list
;;;;     initial is a number
;;;;     increment is a number
;;;;
;;;; Returns:
;;;;     Returns the pair (x y), where
;;;;
;;;;         * x is a list identical to (sequence lis+ initial increment)
;;;;         * y is the number (initial + (# of atoms in lis+) * increment)
;;;;
;;;;  Worst-case asymptotic run-time:
;;;;     O(1 + (number of cons-cells in lis+))
;;;;


(define sequence-atoms-aux
  (lambda (lis+ initial increment)
    (cond
      ((null? lis+) (list '() initial))
      ((atom? (car lis+))
       (let
           ((cdr-result
             (sequence-atoms-aux (cdr lis+) (+ initial increment) increment)))
         (list
          (cons
           (list ': initial (car lis+))
           (car cdr-result))
          (cadr cdr-result))))
      (else
       (let*
           ((car-result
             (sequence-atoms-aux (car lis+) initial increment))
            (cdr-result
             (sequence-atoms-aux (cdr lis+) (cadr car-result) increment)))
         (list
          (cons
           (car car-result)
           (car cdr-result))
          (cadr cdr-result)))))))


;;;;;;;;
;;;;;;;; Procedure (restructure destructured-lis+)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Restructures a previously-destructured list
;;;;;;;;     (See the definition of the procedure "destructure" above.)
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     destructured-lis+ = (destructure lis+), where lis+ is an arbitrarily-complex list
;;;;;;;;
;;;;;;;; Worst-case asymptotic run time:
;;;;;;;;     O(1 + |destructured-lis+|) = O(1 + (# of cons-cells in destructured-lis+)
;;;;;;;;


(define restructure
  (lambda (destructured-lis+)
    (car (restructure-aux (cdr destructured-lis+)))))


;;;;
;;;; Procedure (restructure-aux destructured-sublists-plus-suffix)
;;;;
;;;; Purpose/Returns:
;;;;     Returns the pair ((L1 L2 ... Lm) (y1 ... yk)), where L1, ... , Lm and y1, ... , yk
;;;;     are as defined in the pre-conditions
;;;;
;;;; Pre-conditions:
;;;;     destructured-sublists-plus-suffix is a list of the form
;;;;
;;;;         (x1,1 ... x1,n1 x2,1 ... x2,n2 ... xm,1 ... xm,nm (rp) y1 ... yk)
;;;;
;;;;     where
;;;;
;;;;         (x1,1 ... x1,n1) = (destructure L1), for some arbitrarily-complex list L1
;;;;         (x2,1 ... x2,n2) = (destructure L2), for some arbitrarily-complex list L2
;;;;         ...
;;;;         (xm,1 ... xm,nm) = (destructure Lm), for some arbitrarily-complex list Lm
;;;;
;;;; Worst-case asymptotic run time:
;;;;     O(1 + |destructured-sublists-plus-suffix|)
;;;;


(define restructure-aux
  (lambda (destructured-sublists-plus-suffix)
    (cond
      ((atom? (car destructured-sublists-plus-suffix))
       (let
           ((restructured-cdr (restructure-aux (cdr destructured-sublists-plus-suffix))))
         (list
          (cons (car destructured-sublists-plus-suffix) (car restructured-cdr))
          (cadr restructured-cdr))))
      ((eq? (caar destructured-sublists-plus-suffix) 'rp)
       (list '() (cdr destructured-sublists-plus-suffix)))
      (else
       (let*
           ((restructured-car (restructure-aux (cdr destructured-sublists-plus-suffix)))
            (restructured-cdr (restructure-aux (cadr restructured-car))))
         (list
          (cons (car restructured-car) (car restructured-cdr))
          (cadr restructured-cdr)))))))