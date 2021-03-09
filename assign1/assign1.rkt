#lang scheme

(require (lib "tls.ss" "Luther"))


;;;;;;;;
;;;;;;;; Procedure (up-ramp lis)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Creates an "upward ramp" from the elements of the list lis
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis must be a proper list
;;;;;;;;
;;;;;;;; Returns
;;;;;;;;     ()
;;;;;;;;         when lis = ()
;;;;;;;;     (x0 (x1 (x2 (... (xn-2 (xn-1 (xn)))...))))
;;;;;;;;         when lis = (x0 x1 x2 ... xn-2 xn-1 xn)
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + |lis|)
;;;;;;;;


(define up-ramp
  (lambda (lis)
    (cond
      ((null? lis) '())
      ((null? (cdr lis)) lis)
      (else (cons (car lis) (cons (up-ramp (cdr lis)) '()))))))


;;;;;;;;
;;;;;;;; Procedure (down-ramp lis)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Creates a "downward ramp" from the elements of the list lis
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis must be a proper list
;;;;;;;;
;;;;;;;; Returns
;;;;;;;;     ()
;;;;;;;;         when lis = ()
;;;;;;;;    ((((...(((x0) x1) x2) ...) xn-2) xn-1) xn)
;;;;;;;;         when lis = (x0 x1 x2 ... xn-2 xn-1 xn)
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + |lis|)
;;;;;;;;


(define down-ramp
  (lambda (lis)
    (if
     (null? lis)
     '()
     (down-ramp-aux (cons (car lis) '()) (cdr lis)))))


;;;;
;;;; Auxiliary procedure (down-ramp-aux result lis)
;;;;
;;;; Purpose:
;;;;     Creates a "downward ramp" from the elements of the list lis,
;;;;     with the elements of result as the deepest elements to the right
;;;;
;;;; Pre-conditions:
;;;;     result must be a proper list
;;;;     lis must be a proper list
;;;;
;;;; Returns:
;;;;    ((((...((((x0 ... xm-1) y0) y1) y2) ...) yn-2) yn-1) yn)
;;;;         when result = (x0 ... xm-1) and lis = (y0 y1 y2 ... yn-1 yn)
;;;;
;;;; Worst-case asymptotic run-time:
;;;;     O(1 + |lis|)
;;;;


(define down-ramp-aux
  (lambda (result lis)
    (if
     (null? lis)
     result
     (down-ramp-aux (cons result (cons (car lis) '())) (cdr lis)))))


;;;;
;;;; A needlessly-expensive alternate version
;;;;
;;;; Worst-case asymptotic run-time:
;;;;     O(1 + |lis| ^ 2)
;;;;


(define down-ramp-version-2
  (lambda (lis)
    (cond
      ((null? lis) '())
      ((null? (cdr lis)) lis)
      (else (cons (down-ramp-version-2 (rdc lis)) (cons (rac lis) '()))))))


;;;;
;;;; A more obscure alternate version
;;;;
;;;; Worst-case asymptotic run-time:
;;;;     O(1 + |lis|)
;;;;


(define down-ramp-version-3
  (lambda (lis)
    (twist (up-ramp (rev-linear lis '())))))


;;
;; Auxiliary procedure (twist up-ramp-lis)
;;
;; Purpose:
;;     Constructs a pair-wise reversal of an up-ramp
;;
;; Pre-conditions:
;;     up-ramp-lis must be a proper list of the form (x0 (x1 (x2 (... (xn-1 (xn))...))))
;;
;; Returns:
;;    (((...(((xn) xn-1) ...) x2) x1) x0)
;;         when lis = (x0 (x1 (x2 (... (xn-1 (xn))...))))
;;
;;;; Worst-case asymptotic run-time:
;;     O(1 + |up-ramp-lis|)
;;


(define twist
  (lambda (up-ramp-lis)
    (cond
      ((null? up-ramp-lis) '())
      ((null? (cdr up-ramp-lis)) up-ramp-lis)
      (else (cons (twist (cadr up-ramp-lis)) (cons (car up-ramp-lis) '()))))))


;;;;;;;;
;;;;;;;; Procedure (middlemost lis)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Returns the middlemost element of the list lis
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     lis must be a non-empty proper list
;;;;;;;;
;;;;;;;; Returns:
;;;;;;;;     xj
;;;;;;;;         when lis = (x0 ... xj-1 xj ... x2j-1)
;;;;;;;;         or lis = (x0 ... xj-1 xj xj+1 ... x2j)
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + |lis|)
;;;;;;;;


(define middlemost
  (lambda (lis)
    (middlemost-aux lis lis)))


;;;;
;;;; Auxiliary procedure (middlemost-aux lis count)
;;;;
;;;; Purpose:
;;;;     Returns the middlemost element of the list lis, which contains
;;;;         count elements
;;;;
;;;; Pre-conditions:
;;;;     lis must be a non-empty proper list
;;;;     count must be a proper list
;;;;     |count| <= |lis|
;;;;
;;;; Returns:
;;;;     Element floor(|count| / 2) from lis
;;;;         when lis = (x0 ... xn-1)
;;;;
;;;; Worst-case asymptotic run-time:
;;;;     O(1 + |count|)
;;;;


(define middlemost-aux
  (lambda (lis count)
    (cond
      ((null? count) (car lis))
      ((null? (cdr count)) (car lis))
      (else (middlemost-aux (cdr lis) (cddr count))))))


;;;;;;;;
;;;;;;;; Procedure (fetch path lis)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Returns the element of the lis obtained by following the list path
;;;;;;;;
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     path must be a proper list containing a sequence of zero or more
;;;;;;;;         instance of the symbols 'car and/or 'cdr only.
;;;;;;;;     lis must be a proper list
;;;;;;;;     The first-to-last sequence of symbols 'car and 'cdr in path
;;;;;;;;         corresponds to a chronological sequence of applications of
;;;;;;;;         the car and cdr primitives that can be legally applied to lis
;;;;;;;;         without error (i.e., the path exists wrt lis)
;;;;;;;;
;;;;;;;; Returns:
;;;;;;;;     (x0 (x1 (x2 ... (xn-2 (xn-1 lis)) ...)))
;;;;;;;;         when path = ('x0 'x1 'x2 ... 'xn-2 'xn-1) 
;;;;;;;;
;;;;;;;; Worst-case asymptotic run-time:
;;;;;;;;     O(1 + |path|)
;;;;;;;;


(define fetch
  (lambda (path lis)
    (cond
      ((null? path) lis)
      ((eq? (car path) 'car) (fetch (cdr path) (car lis)))
      (else (fetch (cdr path) (cdr lis))))))


;;;;;;;;
;;;;;;;; Procedure (split subject pattern)
;;;;;;;;
;;;;;;;; Purpose:
;;;;;;;;     Determines if the list pattern occurs anywhere inside the list subject
;;;;;;;;         and, if so, returns the portions before and after the occurrence
;;;;;;;;
;;;;;;;; Pre-conditions:
;;;;;;;;     subject must be a proper list containing symbols only
;;;;;;;;     pattern must be a proper list containing symbols only
;;;;;;;;
;;;;;;;; Returns:
;;;;;;;;     ((x0 ... xi-1) (z0 ... zk-1))
;;;;;;;;         when subject = (x0 ... xi-1 y0 ... yj-1 z0 ... zk-1),
;;;;;;;;         pattern = (y0 ... yj-1),
;;;;;;;;         and pattern does not occur inside (x0 ... xi-1 y0 ... yj-2)
;;;;;;;;     #f otherwise
;;;;;;;;
;;;;;;;; Worst-case asymptotic run time:
;;;;;;;;      O(1 + (|subject| * min(|subject|, |pattern|)))
;;;;;;;;


;;;;
;;;; A very straightforward solution using five auxiliary procedures
;;;;


(define split
  (lambda (subject pattern)
    (if
     (not (occurs-in? subject pattern))
     #f
     (cons (before-match subject pattern) (cons (after-match subject pattern) '())))))


;;
;; Auxiliary procedure (occurs-in? subject pattern)
;;
;; Purpose:
;;     Determines if the list pattern occurs anywhere inside the list subject
;;
;; Pre-conditions:
;;     subject must be a proper list containing symbols only
;;     pattern must be a proper list containing symbols only
;;
;; Returns:
;;     #t
;;         when subject = (x0 ... xi-1 y0 ... yj-1 z0 ... zk-1)
;;         and pattern = (y0 ... yj-1)
;;     #f otherwise
;;
;; Worst-case asymptotic run time:
;;      O(1 + (|subject| * min(|subject|, |pattern|)))
;;


(define occurs-in?
  (lambda (subject pattern)
    (or
     (starts-with? subject pattern)
     (and
      (not (null? subject))
      (occurs-in? (cdr subject) pattern)))))


;;
;; Auxiliary procedure (starts-with? subject pattern)
;;
;; Purpose:
;;     Determines if the list pattern occurs as the initial portion inside
;;     the list subject
;;
;; Pre-conditions:
;;     subject must be a proper list containing symbols only
;;     pattern must be a proper list containing symbols only
;;
;; Returns:
;;     #t
;;         when subject = (x0 ... xi-1 y0 ... yj-1),
;;         and pattern = (x0 ... xi-1)
;;     #f otherwise
;;
;; Worst-case asymptotic run time:
;;      O(1 + min(|subject|, |pattern|))
;;


(define starts-with?
  (lambda (subject pattern)
    (or
     (null? pattern)
     (and
      (eq? (car subject) (car pattern))
      (starts-with? (cdr subject) (cdr pattern))))))


;;
;; Auxiliary procedure (before-match subject pattern)
;;
;; Purpose:
;;     Returns the portion of the list subject that precedes
;;     the first occurrence of pattern inside subject
;;
;; Pre-conditions:
;;     subject must be a proper list containing symbols only
;;     pattern must be a proper list containing symbols only
;;     pattern must occur inside subject
;;
;; Returns:
;;     (x0 ... xi-1)
;;         when subject = (x0 ... xi-1 y0 ... yj-1 z0 ... zk-1),
;;         pattern = (y0 ... yj-1),
;;         and pattern does not occur inside (x0 ... xi-1 y0 ... yj-2)
;;
;; Worst-case asymptotic run time:
;;      O(1 + min(|subject|, |pattern|))
;;


(define before-match
  (lambda (subject pattern)
    (if
     (starts-with? subject pattern)
     '()
     (cons (car subject) (before-match (cdr subject) pattern)))))


;;
;; Auxiliary procedure (after-match subject pattern)
;;
;; Purpose:
;;     Returns the portion of the list subject that follows
;;     the first occurrence of pattern inside subject
;;
;; Pre-conditions:
;;     subject must be a proper list containing symbols only
;;     pattern must be a proper list containing symbols only
;;     pattern must occur inside subject
;;
;; Returns:
;;     (z0 ... zk-1)
;;         when subject = (x0 ... xi-1 y0 ... yj-1 z0 ... zk-1),
;;         pattern = (y0 ... yj-1),
;;         and pattern does not occur inside (x0 ... xi-1 y0 ... yj-2)
;;
;; Worst-case asymptotic run time:
;;      O(1 + min(|subject|, |pattern|))
;;


(define after-match
  (lambda (subject pattern)
    (if
     (starts-with? subject pattern)
     (after-prefix subject pattern)
     (after-match (cdr subject) pattern))))


;;
;; Procedure (after-prefix subject count)
;;
;; Purpose:
;;     Returns the portion of the list subject that follows the first
;;         count elements
;;
;; Pre-conditions:
;;     subject must be a proper list
;;     count must be a proper list
;;     |count| <= |subject|
;;
;; Returns:
;;     (xn ... xm-1)
;;         when subject = (x0 ... xn-1 xn ... xm-1)
;;         and |count| = n
;;
;; Worst-case asymptotic run time:
;;     O(1 + |count|)
;;


(define after-prefix
  (lambda (subject count)
    (if
     (null? count)
     subject
     (after-prefix (cdr subject) (cdr count)))))


;;;;
;;;; A less-straightforward solution that uses an auxiliary procedure
;;;; (one which must be split into two pieces to avoid re-evaluating
;;;; an expression) and uses a utility procedure from lecture
;;;;
;;;; Note that this version has the same worst-case asymptotic run-time as split,
;;;; but more than likely has a smaller constant factor
;;;;


(define split-version-2
  (lambda (subject pattern)
    (split-version-2-aux subject pattern '())))


;;
;; Procedure (split-version-2-aux subject pattern before-match-reversed)
;;
;; Purpose:
;;     Determines if the list pattern occurs anywhere inside
;;     the list subject and, if so, returns the portions before
;;     and after the occurrence
;;
;; Pre-conditions:
;;     subject must be a proper list containing symbols only
;;     pattern must be a proper list containing symbols only
;;
;; Returns:
;;     ((bm-1 ... b0 x0 ... xi-1) (z0 ... zk-1))
;;         when subject = (x0 ... xi-1 y0 ... yj-1 z0 ... zk-1),
;;         pattern = (y0 ... yj-1),
;;         before-match = (b0 ... bm-1),
;;         and pattern does not occur inside (x0 ... xi-1 y0 ... yj-2)
;;     #f otherwise
;;
;; Worst-case asymptotic run time:
;;      O(1 + (|subject| * min(|subject|, |pattern|)))
;;


(define split-version-2-aux
  (lambda (subject pattern before-match-reversed)
    (cond
      ((null? pattern) (list (rev-linear before-match-reversed) subject))
      ((null? subject) #f)
      (else
       (split-version-2-aux-continued
        subject
        pattern
        before-match-reversed
        (split-version-2-at-beginning subject pattern))))))
(define split-version-2-aux-continued
  (lambda (subject pattern before-match-reversed split-at-beginning-subject-pattern)
    (cond
      (split-at-beginning-subject-pattern
       (list
        (rev-linear before-match-reversed)
        (cadr split-at-beginning-subject-pattern)))
      (else
       (split-version-2-aux
        (cdr subject)
        pattern
        (cons (car subject) before-match-reversed))))))


;;
;; Predicate (split-version-2-at-beginning subject pattern)
;;
;; Purpose:
;;     Determines if the initial portion of subject is the same as pattern.
;;
;; Pre-conditions:
;;     subject must be a proper list
;;     pattern must be a proper list

;; Returns:
;;     (() (y0 ... yj-1))
;;         when subject = (x0 ... xi-1 y0 ... yj-1)
;;         and pattern = (x0 ... xi-1)
;;     #f otherwise
;;
;; Worst-case asymptotic run time:
;;     O(1 + min(|subject|, |pattern|))
;;


(define split-version-2-at-beginning
  (lambda (subject pattern)
    (cond
      ((null? pattern) (list '() subject))
      ((or (null? subject) (not (eq? (car subject) (car pattern)))) #f)
      (else (split-version-2-at-beginning (cdr subject) (cdr pattern))))))


;;;;;;;;
;;;;;;;; Utility Procedures (from lecture)
;;;;;;;;


;;;;
;;;; "Right-End" List Operations
;;;;
;;;; All take time O(1 + |lis|)
;;;;


(define rac
  (lambda (lis)
    (if
     (null? (cdr lis))
     (car lis)
     (rac (cdr lis)))))


(define rdc
  (lambda (lis)
    (if
     (null? (cdr lis))
     '()
     (cons (car lis) (rdc (cdr lis))))))


(define snoc
  (lambda (x lis)
    (if
     (null? lis)
     (cons x '())
     (cons (car lis) (snoc x (cdr lis))))))


;;;;
;;;; List-Reversal Operations
;;;;
;;;; All take time O(1 + |lis|)
;;;;


(define rev-linear
  (lambda (lis)
    (rev-linear-aux lis '())))


(define rev-linear-aux
  (lambda (lis result)
    (if
     (null? lis)
     result
     (rev-linear-aux (cdr lis) (cons (car lis) result)))))