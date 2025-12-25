#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    ))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ((new-x (gensym x)))
         (let ((new-env (dict-set env x new-x)))
           (Let
            new-x
            ((uniquify-exp new-env) e)
            ((uniquify-exp new-env) body))))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; Helper predicates for monadic normal form
;; (define (is-atomic? e)
;;   (match e
;;     [(Var _) #t]
;;     [(Int _) #t]
;;     [_ #f]))

;; rco-atom : exp -> (values (listof (cons symbol exp)) exp)
;; Returns a list of (temp-var . complex-expr) pairs and an atomic value
;; If the expression is already atomic, returns empty list and the expression
(define (rco-atom e)
  (match e
    [(Var x) (values '() (Var x))]
    [(Int n) (values '() (Int n))]
    [(Let x rhs body)
     ;; Let is complex, so bind it to a temp
     (let ([temp (gensym "tmp")])
       (values (list (cons temp e)) (Var temp)))]
    [(Prim op es)
     ;; Prim is complex, so bind it to a temp
     (let ([temp (gensym "tmp")])
       (values (list (cons temp e)) (Var temp)))]))

;; build-lets : (listof (cons symbol exp)) exp -> exp
;; Wraps an expression in a series of let bindings
(define (build-lets bindings body)
  (match bindings
    ['() body]
    [(cons (cons temp expr) rest)
     (Let temp (rco-exp expr) (build-lets rest body))]))

;; Main traversal for removing complex operands
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     ;; Process all arguments using rco-atom
     ;; Collect bindings and atomic values
      (define results (for/list ([arg es])
                        (define-values (arg-binds arg-atom) (rco-atom arg))
                        (cons arg-binds arg-atom)))
        (let* ([body (Prim op (map cdr results))] [bindings (append* (map car results))])
        (build-lets bindings body))]
    [_ (error "rco-exp: unexpected expression: ~a" e)]))

;; remove_complex_opera* : Lvar -> Lvar^mon
;; transform to monadic normal form
(define (remove_complex_opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-tail : exp -> tail
;; should be applied to tail position expressions
(define (explicate_tail e) (match e
  [(Var x) (Return (Var x))]
  [(Int n) (Return (Int n))]
  [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
  [(Prim op es) (Return (Prim op es))]
  [_ (error "explicate_tail: unexpected expression: " e)]))

;; explicate-assign : exp -> var -> tail -> tail
;; shoulf be applied to the expressions that occur right-hand side let
(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [_ (error "explicate_assign: unexpected expression: " e)]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate_tail body))))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
      ;; Uncomment the following passes as you finish them.
      ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
      ("remove complex operands" ,remove_complex_opera* ,interp_Lvar ,type-check-Lvar)
      ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
      ;; ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
      ;; ("assign homes" ,assign-homes ,interp-x86-0)
      ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
      ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
      ))
