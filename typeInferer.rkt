#lang plai

(print-only-errors #t)

; constraint-list=? : Constraint list -> Constraint list -> Bool
; signals an error if arguments are not variants of Constraint
(define ((constraint-list=? lc1) lc2)
  (define htlc1 (make-hash))
  (define htlc2 (make-hash))
  (or (andmap (lambda (c1 c2)
                (and
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-lhs c1) (eqc-lhs c2))
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-rhs c1) (eqc-rhs c2))))
              lc1 lc2)
      (error 'constraint-list=?
             "~s and ~a are not equal (modulo renaming)"
             lc1 lc2)))

; type=?/mapping : hash hash Type Type -> Bool
; determines if types are equal modulo renaming
(define (type=?/mapping ht1 ht2 t1 t2)
  (define (teq? t1 t2)
    (type=?/mapping ht1 ht2 t1 t2))
  (cond
    [(and (t-num? t1) (t-num? t2)) true]
    [(and (t-bool? t1) (t-bool? t2)) true]
    [(and (t-list? t1) (t-list? t2))
     (teq? (t-list-elem t1) (t-list-elem t2))]
    [(and (t-fun? t1) (t-fun? t2))
     (and (teq? (t-fun-arg t1) (t-fun-arg t2))
          (teq? (t-fun-result t1) (t-fun-result t2)))]
    [(and (t-var? t1) (t-var? t2))
     (local ([define v1 ; the symbol that ht1 says that t1 maps to
               (hash-ref
                ht1 (t-var-v t1)
                (lambda ()
                  ; if t1 doesn't map to anything, it's the first
                  ; time we're seeing it, so map it to t2
                  (hash-set! ht1 (t-var-v t1) (t-var-v t2))
                  (t-var-v t2)))]
             [define v2
               (hash-ref
                ht2 (t-var-v t2)
                (lambda ()
                  (hash-set! ht2 (t-var-v t2) (t-var-v t1))
                  (t-var-v t1)))])
       ; we have to check both mappings, so that distinct variables
       ; are kept distinct. i.e. a -> b should not be isomorphic to
       ; c -> c under the one-way mapping a => c, b => c.
       (and (symbol=? (t-var-v t2) v1)
            (symbol=? (t-var-v t1) v2)))]
    [(and (Type? t1) (Type? t2)) false]
    [else (error 'type=? "either ~a or ~a is not a Type" t1 t2)]))
 
; type=? Type -> Type -> Bool
; signals an error if arguments are not variants of Type
(define ((type=? t1) t2)
  (or (type=?/mapping (make-hash) (make-hash) t1 t2)
      ; Unfortunately, test/pred simply prints false;
      ; this helps us see what t2 was.
      (error 'type=?
             "~s and ~a are not equal (modulo renaming)"
             t1 t2)))

(define-type Expr
  [num (n number?)]
  [id (v symbol?)]
  [bool (b boolean?)]
  [bin-num-op (op procedure?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
  [with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [rec-with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id symbol?) (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [tempty]
  [tcons (first Expr?) (rest Expr?)]
  [tfirst (e Expr?)]
  [trest (e Expr?)]
  [istempty (e Expr?)])

;; (listof (list/c symbol? (number? number? .. -> .. number?))
;; datat structure contains a mappnig from operator symbol to their 
;; definitions
(define op-table
  (list 
   (list '+ +)
   (list '- -)
   (list '* *)))

;; lookup-op op -> or/c prodedure? false/c
;; op : symbol?
;; extracts definiton of an operator or false if not in op-table
(define (lookup-op op)
   (if (pair? (assoc op op-table))
    (second (assoc op op-table)) #f))

;; TESTS
(test (lookup-op '+) +)
(test (lookup-op '-) -)
(test (lookup-op '^) #f)
(test (lookup-op '*) *)
(test (lookup-op '%) #f)
    
;; Purpose: Test for being a valid identifier
;; Contract: (any?) -> boolean?
(define (valid-id? id)
  #t)

;; Helper function to abstract this operation
(define (eqSymbol? x sexp)
  (and (symbol? (first sexp)) (symbol=? x (first sexp))))

;; Helper function to abstract this operation
(define (Length? num sexp)
  (= (length sexp) num))

; Purpose: Parses the symbol expression according to the 
; abstract syntax tree
; Contract: parse : s-expression -> Expr
(define (parse sexp)
  (cond
    [(empty? sexp) (error "Parse: expected non empty sexpr")]
    [(number? sexp) (num sexp)]
     [(and (symbol? sexp) (symbol=? 'tempty sexp)) (tempty)]
    [(symbol? sexp) 
     (if (or (symbol=? sexp 'true) (symbol=? sexp 'false))
         (if (symbol=? sexp 'true)
             (bool #t)
             (bool #f))
         (if (valid-id? sexp)
             (id sexp)
             (error "Parse: invalid identifier")))]
    [(list? sexp)
     (cond
       [(lookup-op (first sexp))
        (if (Length? 3 sexp)
            (bin-num-op (lookup-op (first sexp))
                        (parse (second sexp))
                        (parse (third sexp)))
            (error "Parse: bin-num-op"))]
       [(eqSymbol? 'iszero sexp)
        (if (Length? 2 sexp)
            (iszero (parse (second sexp)))
            (error "Parse: iszero"))]
       [(eqSymbol? 'bif sexp)
        (if (Length? 4 sexp)
            (bif (parse (second sexp))
                 (parse (third sexp))
                 (parse (fourth sexp)))
            (error "Parse: bif"))]
        [(eqSymbol? 'with sexp)
        (if (Length? 3 sexp)
            (with (first (second sexp))
                  (parse (second (second sexp)))
                  (parse (third sexp)))
            (error "Parse: with"))]
       [(eqSymbol? 'fun sexp)
        (if (Length? 3 sexp)
            (fun 
             (first (second sexp))
             (parse (third sexp)))
            (error "Parse: fun"))]
        [(eqSymbol? 'rec sexp)
        (if (Length? 3 sexp)
            (rec-with
             (first (second sexp))
             (parse (second (second sexp)))
             (parse (third sexp)))
            (error "Parse: rec"))]
       [(eqSymbol? 'tcons sexp)
        (if (Length? 3 sexp)
            (tcons (parse (second sexp))
                   (parse (third sexp)))
            (error "Parse: tcons"))]
       [(eqSymbol? 'tfirst sexp)
        (if (Length? 2 sexp)
            (tfirst (parse (second sexp)))
            (error "Parse: tfirst"))]
       [(eqSymbol? 'trest sexp)
        (if (Length? 2 sexp)
            (trest (parse (second sexp)))
            (error "Parse: trest"))]
       [(eqSymbol? 'tempty? sexp)
        (if (Length? 2 sexp)
            (istempty (parse (second sexp)))
            (error "Parse: tempty?"))]
       [else
        (if (Length? 2 sexp)
            (app (parse (first sexp))
                 (parse (second sexp)))
            (error "Parse: app"))]
     )]
     [else
      (if (boolean? sexp)
          (id sexp)
          (error "Parse: expected expr syntax"))]))

(define (tp toParse value)
  (test (parse toParse) value))
(define (tpe toParse value)
  (test/exn (parse toParse) value))

;; PARSER TESTS

;; num
(test (parse '1) (num 1))
(test (parse '-1) (num -1))
(test (parse '100) (num 100))
(test (parse '1e11) (num 1e11))

;; true/false
(test (parse 'true) (bool true))
(test (parse 'false) (bool false))
(test (parse 'true) (bool #t))
(test (parse 'false) (bool #f))

;; binop-num-op
(test (parse '(+ 1 2)) (bin-num-op + (num 1) (num 2)))
(test/exn (parse '(+ 1)) "Parse: bin-num-op")
(test/exn (parse '(+ 1 2 3)) "Parse: bin-num-op")
(test (parse '(+ hi bob)) (bin-num-op + (id 'hi) (id 'bob)))
(test (parse '(- 1 2)) (bin-num-op - (num 1) (num 2)))
(test/exn (parse '(- 1)) "Parse: bin-num-op")
(test/exn (parse '(- 1 2 3)) "Parse: bin-num-op")
(test (parse '(- hi bob)) (bin-num-op - (id 'hi) (id 'bob)))
(test (parse '(* 1 2)) (bin-num-op * (num 1) (num 2)))
(test/exn (parse '(* 1)) "Parse: bin-num-op")
(test/exn (parse '(* 1 2 3)) "Parse: bin-num-op")
(test (parse '(* hi bob)) (bin-num-op * (id 'hi) (id 'bob)))
;; iszero
(test (parse '(iszero 5)) (iszero (num 5)))
(test (parse '(iszero hi)) (iszero (id 'hi)))
(test (parse '(iszero true)) (iszero (bool true)))
;; bif
(test (parse '(bif 1 1 1)) 
      (bif (num 1) (num 1) (num 1)))
(test (parse '(bif a b c))
      (bif (id 'a) (id 'b) (id 'c)))
(test (parse '(bif (bif a b c) b c))
      (bif (bif (id 'a) (id 'b) (id 'c)) (id 'b) (id 'c)))
(test (parse '(bif 1 (with (hello 5) hi) a))
      (bif (num 1) (with 'hello (num 5) (id 'hi)) (id 'a)))
;; id
(test (parse 'hi) (id 'hi))
(test (parse 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)
      (id 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa))
;; with
(test (parse '(with (hello 5) hi)) 
      (with 'hello (num 5) (id 'hi)))
(tp '(with (x 1) x) (with 'x (num 1) (id 'x)))
(tp '(with (x (+ 1 2)) x) 
    (with 'x (bin-num-op + (num 1) (num 2)) (id 'x)))
(tp '(with (x 1) (+ 1 x)) 
    (with 'x (num 1) (bin-num-op + (num 1) (id 'x))))
(tp '(with (x ((fun (x) x) true)) x)
    (with 'x (app (fun 'x (id 'x)) (bool true)) (id 'x)))
;; fun
(test (parse '(fun (hi) 5)) 
      (fun 'hi (num 5)))
(test (parse '(fun (x) (+ x 5))) 
      (fun 'x (bin-num-op + (id 'x) (num 5))))
(tp '(fun (x) x) (fun 'x (id 'x)))
(tp '(fun (x) (fun (y) (+ x y))) 
    (fun 'x (fun 'y (bin-num-op + (id 'x) (id 'y)))))
;; rec 
(test (parse '(rec (hi 2) 5)) (rec-with 'hi (num 2) (num 5)))
(tp '(rec (x 1) x) (rec-with 'x (num 1) (id 'x)))
(tp '(rec (x (+ 1 2)) x) 
    (rec-with 'x (bin-num-op + (num 1) (num 2)) (id 'x)))
(tp '(rec (x 1) (+ 1 x)) 
    (rec-with 'x (num 1) (bin-num-op + (num 1) (id 'x))))
(tp '(rec (x ((fun (x) x) true)) x)
    (rec-with 'x (app (fun 'x (id 'x)) (bool true)) (id 'x)))
;; app
(test (parse '(5 5)) (app (num 5) (num 5)))
(tp '((fun (x) x) 1) (app (fun 'x (id 'x)) (num 1)))
(tp '((fun (x) (fun (y) (+ x y))) (+ 1 2)) 
    (app (fun 'x (fun 'y (bin-num-op + (id 'x) (id 'y)))) 
         (bin-num-op + (num 1) (num 2))))
;; tempty
(test (parse 'tempty) (tempty))
;; tcons
(test (parse '(tcons 5 5)) (tcons (num 5) (num 5)))
(tp '(tcons 1 tempty) (tcons (num 1) (tempty)))
(tp '(tcons true tempty) (tcons (bool true) (tempty)))
(tp '(tcons (+ 1 2) tempty) (tcons (bin-num-op + (num 1) (num 2)) (tempty)))
(tp '(tcons (fun (x) x) tempty) (tcons (fun 'x (id 'x)) (tempty)))
(tp '(tcons 1 (tcons 2 tempty)) (tcons (num 1) (tcons (num 2) (tempty))))
(tp '(tcons 1 (tcons true tempty))
    (tcons (num 1) (tcons (bool true) (tempty))))
(tp '(tcons tempty tempty) (tcons (tempty) (tempty)))
;; tempty?
(test (parse '(tempty? 5)) (istempty (num 5)))
;; tfirst 
(test (parse '(tfirst 5)) (tfirst (num 5)))
(tp '(tfirst (tcons 1 tempty)) (tfirst (tcons (num 1) (tempty))))
(tp '(tfirst tempty) (tfirst (tempty)))
(tp '(tfirst (tcons true tempty)) (tfirst (tcons (bool true) (tempty))))
(tp '(tfirst (tcons false tempty)) (tfirst (tcons (bool false) (tempty))))
;; trest
(test (parse '(trest 5)) (trest (num 5)))
(tp '(trest (tcons 1 tempty)) (trest (tcons (num 1) (tempty))))
(tp '(trest tempty) (trest (tempty)))
(tp '(trest (tcons true tempty)) (trest (tcons (bool true) (tempty))))
(tp '(trest (tcons false tempty)) (trest (tcons (bool false) (tempty))))
;; istempty
(tp '(tempty? tempty) (istempty (tempty)))
(tp '(tempty? (tcons true tempty)) (istempty (tcons (bool true) (tempty))))
(tp '(tempty? (tcons false tempty)) (istempty (tcons (bool false) (tempty))))

;; 3.19.3 Alpha Renaming
;; Purpose: Renames all identifiers in e to a new unique identifier. 
;; Contract: (alpha-vary e) -> Expr?
;;           e : Expr? 
(define (alpha-vary e [h-map (make-immutable-hasheq)])
  (type-case Expr e
   [num (n) e]
    [id (v) (id (hash-ref h-map v (λ () (error "alpha-vary: unbound id"))))]
    [bool (b) e]
    [bin-num-op (op left right) 
                (bin-num-op op (alpha-vary left h-map)(alpha-vary right h-map))]
    [iszero (e1) (iszero (alpha-vary e1 h-map))]
    [bif (e1 e2 e3) (bif (alpha-vary e1 h-map) (alpha-vary e2 h-map) (alpha-vary e3 h-map))]
    [with (bound-id bound-body body) 
      (local ((define newSym (gensym bound-id)))
        (with
          newSym 
          (alpha-vary bound-body (hash-set h-map bound-id newSym))
          (alpha-vary body (hash-set h-map bound-id newSym))))]
    [rec-with (bound-id bound-body body) 
      (local ((define newSym (gensym bound-id)))
        (rec-with 
          newSym 
          (alpha-vary bound-body h-map)
          (alpha-vary body (hash-set h-map bound-id newSym))))]
    [fun (arg-id body)
      (local ((define newSym (gensym arg-id)))
        (fun
          newSym
          (alpha-vary body (hash-set h-map arg-id newSym))))]
    [app (fun-expr arg-expr) (app (alpha-vary fun-expr h-map) (alpha-vary arg-expr h-map))]
    [tempty () e]
    [tcons (first rest) (tcons (alpha-vary first h-map) (alpha-vary rest h-map))]
    [istempty (e1) (istempty (alpha-vary e1 h-map))]
    [tfirst (e1) (tfirst (alpha-vary e1 h-map))]
    [trest (e1) (trest (alpha-vary e1 h-map))]))



;; TESTS FOR ALPHA-VARY
;; num
(test (alpha-vary (parse '1)) (num 1))
(test (alpha-vary (parse '-1)) (num -1))
;; binop
(test (alpha-vary (parse '(+ 1 2))) (bin-num-op + (num 1) (num 2)))
(test (alpha-vary (parse '(- 1 2))) (bin-num-op - (num 1) (num 2)))
(test (alpha-vary (parse '(* 1 2))) (bin-num-op * (num 1) (num 2)))
;; bool
(test (alpha-vary (parse 'true)) (bool #t))
(test (alpha-vary (parse 'false)) (bool #f))
;; iszero
(test (alpha-vary (parse '(iszero 1))) (iszero (num 1)))
;; bif
(test (alpha-vary (parse '(bif 1 2 3))) (bif (num 1) (num 2) (num 3)))
;; unbound identifier
(test/exn (alpha-vary (parse 'hi)) "alpha-vary")
;; with
;(test (alpha-vary (parse '(with (id 5) 10)))
;      (with 'id97080 (num 5) (num 10)))
;(test (alpha-vary (parse '(with (x 1) x)))
;      (with 'x113167 (num 1) (id 'x113167)))
;(test (alpha-vary (parse '(with (x 1) (with (x x) x))))         
;     (with 'x113848 (num 1) (with 'x113849 (id 'x113849) (id 'x113849))))

;; rec-with
;(alpha-vary (parse '(rec (x 1) x)))
;       (rec-with 'x114632 (num 1) (id 'x114632))
;(test (alpha-vary (parse '(rec (id 5) 10)))(rec-with 'id98442 (num 5) (num 10)))
;(alpha-vary (parse '(rec (x 1) (rec (x x) x))))
;       (rec-with 'x115115 (num 1) (rec-with 'x115116 (id 'x115115) (id 'x115116)))
; (alpha-vary (parse '(rec (x (fun (x) x)) (x 1))))
;     (rec-with 'x115501 (fun 'x115502 (id 'x115502)) (app (id 'x115501) (num 1)))
;
;; fun
;(alpha-vary (parse '(fun (x) x) ))
;     (fun 'x116021 (id 'x116021))
;(alpha-vary (parse '(fun (x) (fun (x) x))))
;    (fun 'x116297 (fun 'x116298 (id 'x116298)))
;(alpha-vary (parse '(fun (x) (fun (y) x))))
;    (fun 'x116568 (fun 'y116569 (id 'x116568)))
;; app

;; tempty
(test (alpha-vary (parse 'tempty))(tempty))
;; tcons
(test (alpha-vary (parse '(tcons 1 tempty))) (tcons (num 1) (tempty)))
(test (alpha-vary (parse '(tcons true tempty))) (tcons (bool true) (tempty)))
;; tempty?
(test (alpha-vary (parse '(tempty? 1))) (istempty (num 1)))
;; tfirst
(test (alpha-vary (parse '(tfirst 1))) (tfirst (num 1)))
;; trest
(test (alpha-vary (parse '(trest 1))) (trest (num 1)))


(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)])
 
(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])

;; 3.19.4 Constraint Generation

;; Purpose: Returns the constraints generated by e.e-id 
;; Contract: (generate-constraints e-id e) -> (listof Constraints)
;;           e-id : symbol?
;;           e : Expr?
(define (generate-constraints e-id e)
  (type-case Expr e
    [num (n) (list (eqc (t-var e-id) (t-num)))]
    [id (v) (list (eqc (t-var e-id) (t-var v)))]
    [bool (b) (list (eqc (t-var e-id) (t-bool)))]
    [bin-num-op (op left right)
                (local ((define nm-left (gensym))
                        (define nm-right (gensym)))
                (append
                 (generate-constraints nm-left left)
                 (generate-constraints nm-right right)
                 (list (eqc (t-var e-id) (t-num))
                       (eqc (t-var nm-left) (t-num))
                       (eqc (t-var nm-right) (t-num)))))]
    [iszero (e1) 
            (local ((define nm-e (gensym)))
              (append 
               (generate-constraints nm-e e1)
               (list (eqc (t-var e-id) (t-bool))
                     (eqc (t-var nm-e) (t-num)))))]
    [bif (e1 e2 e3) 
         (local ((define nm-e1 (gensym))
                 (define nm-e2 (gensym))
                 (define nm-e3 (gensym)))
           (append 
            (generate-constraints nm-e1 e1)
            (generate-constraints nm-e2 e2)
            (generate-constraints nm-e3 e3)
            (list (eqc (t-var e-id) (t-var nm-e2))
                  (eqc (t-var e-id) (t-var nm-e3))
                  (eqc (t-var nm-e1) (t-bool)))))]
    [with (bound-id bound-body body) 
          (local ((define nm-bound-id (gensym))
                  (define nm-bound-body (gensym))
                  (define nm-body (gensym)))
            (append
             (generate-constraints nm-bound-body bound-body)
             (generate-constraints nm-body body)
             (list (eqc (t-var e-id) (t-var nm-body)))))]
    [rec-with (bound-id bound-body body) 
              (local ((define nm-bound-id (gensym))
                      (define nm-bound-body (gensym))
                      (define nm-body (gensym)))
                (append
                 (generate-constraints nm-bound-body bound-body)
                 (generate-constraints nm-body body)
                 (list (eqc (t-var e-id) (t-var nm-body)))))]
    [fun (arg-id body) 
         (local ((define nm-arg-id (gensym))
                 (define nm-body (gensym)))
           (append
            (generate-constraints nm-body body)
            (list
              (eqc (t-var arg-id) (t-var nm-arg-id))
              (eqc (t-var e-id) (t-fun (t-var nm-arg-id) (t-var nm-body))))))]
    [app (fun-expr arg-expr) 
         (local ((define nm-fun-expr (gensym))
                 (define nm-arg-expr (gensym))
                 (define nm-result (gensym)))
           (append
            (generate-constraints nm-fun-expr fun-expr)
            (generate-constraints nm-arg-expr arg-expr)
            (list
              (eqc (t-var e-id) (t-var nm-result))
              (eqc (t-var nm-fun-expr) (t-fun (t-var nm-arg-expr) (t-var nm-result))))))]
    [tempty ()
         (local ((define nm-elem (gensym)))
           (list (eqc (t-var e-id) (t-list (t-var nm-elem)))))]
    [tcons (first rest) 
           (local ((define nm-first (gensym))
                   (define nm-rest (gensym)))
           (append
            (generate-constraints nm-first first)
            (generate-constraints nm-rest rest)
            (list (eqc (t-var e-id) (t-list (t-var nm-first)))
                  (eqc (t-var nm-rest) (t-list (t-var nm-first))))))]
    [istempty (e1) 
              (local ((define nm-e1 (gensym)))
                (append
                 (generate-constraints nm-e1 e1)
                 (list (eqc (t-var e-id) (t-bool))
                       (eqc (t-var nm-e1) (t-list (t-var (gensym)))))))]
    [tfirst (e1) 
            (local ((define nm-e1 (gensym)) (define nm-elem (gensym)))
                (append
                 (generate-constraints nm-e1 e1)
                 (list (eqc (t-var e-id) (t-var nm-elem))
                       (eqc (t-var nm-e1) (t-list (t-var nm-elem))))))]
    [trest (e1) 
           (local ((define nm-e1 (gensym)) (define nm-elem (gensym)))
                (append
                 (generate-constraints nm-e1 e1)
                 (list (eqc (t-var e-id) (t-list (t-var nm-elem)))
                       (eqc (t-var nm-e1) (t-list (t-var nm-elem))))))]))

;; TESTS FOR CONSTRAINT GENERATION
; num
(test (generate-constraints 'x (parse '5)) (list (eqc (t-var 'x) (t-num))))
; id
(test (generate-constraints 'x (parse 'hi)) (list (eqc (t-var 'x) (t-var 'hi))))
;; bool
(test (generate-constraints 'x (parse 'true)) (list (eqc (t-var 'x) (t-bool))))
(test (generate-constraints 'x (parse 'false)) (list (eqc (t-var 'x) (t-bool))))
;; bin-num-op
((constraint-list=? 
 (generate-constraints 'x (parse '(+ 1 2)))) 
      (list (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num)) 
            (eqc (t-var 'x) (t-num)) 
            (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num))))
((constraint-list=? 
  (generate-constraints 'x (parse '(- 1 2)))) 
      (list (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num)) 
            (eqc (t-var 'x) (t-num)) 
            (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num))))
((constraint-list=? 
  (generate-constraints 'x (parse '(* 1 2)))) 
      (list (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num)) 
            (eqc (t-var 'x) (t-num)) 
            (eqc (t-var 'g95740) (t-num)) 
            (eqc (t-var 'g95741) (t-num))))
((constraint-list=? 
  (generate-constraints 'x (parse '(+ (+ 3 2) (+ 1 2)))))
(list
 (eqc (t-var 'g106509) (t-num))
 (eqc (t-var 'g106510) (t-num))
 (eqc (t-var 'g106507) (t-num))
 (eqc (t-var 'g106509) (t-num))
 (eqc (t-var 'g106510) (t-num))
 (eqc (t-var 'g106511) (t-num))
 (eqc (t-var 'g106512) (t-num))
 (eqc (t-var 'g106508) (t-num))
 (eqc (t-var 'g106511) (t-num))
 (eqc (t-var 'g106512) (t-num))
 (eqc (t-var 'x) (t-num))
 (eqc (t-var 'g106507) (t-num))
 (eqc (t-var 'g106508) (t-num))))
;; iszero
((constraint-list=? 
  (generate-constraints 'x (parse '(iszero 0))))
(list (eqc (t-var 'g109887) (t-num)) 
      (eqc (t-var 'x) (t-bool)) 
      (eqc (t-var 'g109887) (t-num))))
((constraint-list=?
  (generate-constraints 'x (parse '(iszero hi))))
 (list
  (eqc (t-var 'g112321) (t-var 'hi))
  (eqc (t-var 'x) (t-bool))
  (eqc (t-var 'g112321) (t-num))))
((constraint-list=?
  (generate-constraints 'x (parse '(iszero (+ 1 2)))))
(list
 (eqc (t-var 'g113431) (t-num))
 (eqc (t-var 'g113432) (t-num))
 (eqc (t-var 'g113430) (t-num))
 (eqc (t-var 'g113431) (t-num))
 (eqc (t-var 'g113432) (t-num))
 (eqc (t-var 'x) (t-bool))
 (eqc (t-var 'g113430) (t-num))))
;; bif
((constraint-list=?
  (generate-constraints 'x (parse '(bif true true true))))
(list
 (eqc (t-var 'g115722) (t-bool))
 (eqc (t-var 'g115723) (t-bool))
 (eqc (t-var 'g115724) (t-bool))
 (eqc (t-var 'x) (t-var 'g115723))
 (eqc (t-var 'x) (t-var 'g115724))
 (eqc (t-var 'g115722) (t-bool))))
((constraint-list=?
  (generate-constraints 'x (parse '(bif 1 1 1))))
(list
 (eqc (t-var 'g116228) (t-num))
 (eqc (t-var 'g116229) (t-num))
 (eqc (t-var 'g116230) (t-num))
 (eqc (t-var 'x) (t-var 'g116229))
 (eqc (t-var 'x) (t-var 'g116230))
 (eqc (t-var 'g116228) (t-bool))))
((constraint-list=?
  (generate-constraints 'x (parse '(bif true 1 1))))
(list
 (eqc (t-var 'g116862) (t-bool))
 (eqc (t-var 'g116863) (t-num))
 (eqc (t-var 'g116864) (t-num))
 (eqc (t-var 'x) (t-var 'g116863))
 (eqc (t-var 'x) (t-var 'g116864))
 (eqc (t-var 'g116862) (t-bool))))
((constraint-list=?
  (generate-constraints 'x (parse '(bif true true 1))))
(list
 (eqc (t-var 'g117371) (t-bool))
 (eqc (t-var 'g117372) (t-bool))
 (eqc (t-var 'g117373) (t-num))
 (eqc (t-var 'x) (t-var 'g117372))
 (eqc (t-var 'x) (t-var 'g117373))
 (eqc (t-var 'g117371) (t-bool))))
;; with
((constraint-list=? (generate-constraints 'x (parse '(with (x 1) x))))
(list
 (eqc (t-var 'g120360) (t-num))
 (eqc (t-var 'g120361) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g120361))))
((constraint-list=? (generate-constraints 'x (parse '(with (x 1) true))))
(list
 (eqc (t-var 'g124054) (t-num))
 (eqc (t-var 'g124055) (t-bool))
 (eqc (t-var 'x) (t-var 'g124055))))
((constraint-list=? 
  (generate-constraints 'x (parse '(with (x (fun (x) 1)) (fun (y) y)))))
(list
 (eqc (t-var 'g124786) (t-num))
 (eqc (t-var 'x) (t-var 'g124785))
 (eqc (t-var 'g124783) (t-fun (t-var 'g124785) (t-var 'g124786)))
 (eqc (t-var 'g124788) (t-var 'y))
 (eqc (t-var 'y) (t-var 'g124787))
 (eqc (t-var 'g124784) (t-fun (t-var 'g124787) (t-var 'g124788)))
 (eqc (t-var 'x) (t-var 'g124784))))
((constraint-list=? 
  (generate-constraints 'x (parse '(with (x ((fun (x) x) true)) x))))
(list
 (eqc (t-var 'g125179) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g125178))
 (eqc (t-var 'g125175) (t-fun (t-var 'g125178) (t-var 'g125179)))
 (eqc (t-var 'g125176) (t-bool))
 (eqc (t-var 'g125173) (t-var 'g125177))
 (eqc (t-var 'g125175) (t-fun (t-var 'g125176) (t-var 'g125177)))
 (eqc (t-var 'g125174) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g125174))))
;; rec
((constraint-list=? 
 (generate-constraints 'x (parse '(rec (f f) f))))
(list
 (eqc (t-var 'g125765) (t-var 'f))
 (eqc (t-var 'g125766) (t-var 'f))
 (eqc (t-var 'x) (t-var 'g125766))))
((constraint-list=? 
  (generate-constraints 'x 
    (parse '(rec (f (fun (x) 
      (bif (iszero x) x (+ x (f (- x 1)))))) f))))
(list
 (eqc (t-var 'g126580) (t-var 'x))
 (eqc (t-var 'g126577) (t-bool))
 (eqc (t-var 'g126580) (t-num))
 (eqc (t-var 'g126578) (t-var 'x))
 (eqc (t-var 'g126581) (t-var 'x))
 (eqc (t-var 'g126583) (t-var 'f))
 (eqc (t-var 'g126586) (t-var 'x))
 (eqc (t-var 'g126587) (t-num))
 (eqc (t-var 'g126584) (t-num))
 (eqc (t-var 'g126586) (t-num))
 (eqc (t-var 'g126587) (t-num))
 (eqc (t-var 'g126582) (t-var 'g126585))
 (eqc (t-var 'g126583) (t-fun (t-var 'g126584) (t-var 'g126585)))
 (eqc (t-var 'g126579) (t-num))
 (eqc (t-var 'g126581) (t-num))
 (eqc (t-var 'g126582) (t-num))
 (eqc (t-var 'g126576) (t-var 'g126578))
 (eqc (t-var 'g126576) (t-var 'g126579))
 (eqc (t-var 'g126577) (t-bool))
 (eqc (t-var 'x) (t-var 'g126575))
 (eqc (t-var 'g126573) (t-fun (t-var 'g126575) (t-var 'g126576)))
 (eqc (t-var 'g126574) (t-var 'f))
 (eqc (t-var 'x) (t-var 'g126574))))
;; fun
((constraint-list=? 
  (generate-constraints 'x (parse '(fun (x) (fun (y) (+ x y))))))
(list
 (eqc (t-var 'g127708) (t-var 'x))
 (eqc (t-var 'g127709) (t-var 'y))
 (eqc (t-var 'g127707) (t-num))
 (eqc (t-var 'g127708) (t-num))
 (eqc (t-var 'g127709) (t-num))
 (eqc (t-var 'y) (t-var 'g127706))
 (eqc (t-var 'g127705) (t-fun (t-var 'g127706) (t-var 'g127707)))
 (eqc (t-var 'x) (t-var 'g127704))
 (eqc (t-var 'x) (t-fun (t-var 'g127704) (t-var 'g127705)))))
((constraint-list=? 
  (generate-constraints 'x (parse '(fun (x) 1))))
(list
 (eqc (t-var 'g128077) (t-num))
 (eqc (t-var 'x) (t-var 'g128076))
 (eqc (t-var 'x) (t-fun (t-var 'g128076) (t-var 'g128077)))))
((constraint-list=? 
  (generate-constraints 'x (parse '(fun (x) x))))
(list
 (eqc (t-var 'g128777) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g128776))
 (eqc (t-var 'x) (t-fun (t-var 'g128776) (t-var 'g128777)))))
;; app
((constraint-list=? 
  (generate-constraints 'x (parse '((fun (x) 1) 1))))
(list
 (eqc (t-var 'g129124) (t-num))
 (eqc (t-var 'x) (t-var 'g129123))
 (eqc (t-var 'g129120) (t-fun (t-var 'g129123) (t-var 'g129124)))
 (eqc (t-var 'g129121) (t-num))
 (eqc (t-var 'x) (t-var 'g129122))
 (eqc (t-var 'g129120) (t-fun (t-var 'g129121) (t-var 'g129122)))))
((constraint-list=? 
  (generate-constraints 'x (parse '((fun (x) x) 1))))
(list
 (eqc (t-var 'g129698) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g129697))
 (eqc (t-var 'g129694) (t-fun (t-var 'g129697) (t-var 'g129698)))
 (eqc (t-var 'g129695) (t-num))
 (eqc (t-var 'x) (t-var 'g129696))
 (eqc (t-var 'g129694) (t-fun (t-var 'g129695) (t-var 'g129696)))))
((constraint-list=? 
  (generate-constraints 'x (parse '(+ 1 ((fun (x) x) (tfirst tempty))))))
(list
 (eqc (t-var 'g130399) (t-num))
 (eqc (t-var 'g130405) (t-var 'x))
 (eqc (t-var 'x) (t-var 'g130404))
 (eqc (t-var 'g130401) (t-fun (t-var 'g130404) (t-var 'g130405)))
 (eqc (t-var 'g130406) (t-list (t-var 'g130408)))
 (eqc (t-var 'g130402) (t-var 'g130407))
 (eqc (t-var 'g130406) (t-list (t-var 'g130407)))
 (eqc (t-var 'g130400) (t-var 'g130403))
 (eqc (t-var 'g130401) (t-fun (t-var 'g130402) (t-var 'g130403)))
 (eqc (t-var 'x) (t-num))
 (eqc (t-var 'g130399) (t-num))
 (eqc (t-var 'g130400) (t-num))))
;; tempty
((constraint-list=?
  (generate-constraints 'x (parse 'tempty)))
(list (eqc (t-var 'x) (t-list (t-var 'any)))))
;; tcons
((constraint-list=?
  (generate-constraints 'x (parse '(tcons 1 1))))
(list
 (eqc (t-var 'g138032) (t-num))
 (eqc (t-var 'g138033) (t-num))
 (eqc (t-var 'x) (t-list (t-var 'g138032)))
 (eqc (t-var 'g138033) (t-list (t-var 'g138032)))))
((constraint-list=?
  (generate-constraints 'x (parse '(tcons true 1))))
(list
 (eqc (t-var 'g138516) (t-bool))
 (eqc (t-var 'g138517) (t-num))
 (eqc (t-var 'x) (t-list (t-var 'g138516)))
 (eqc (t-var 'g138517) (t-list (t-var 'g138516)))))
((constraint-list=?
  (generate-constraints 'x (parse '(tcons true nemtpy))))
(list
 (eqc (t-var 'g139201) (t-bool))
 (eqc (t-var 'g139202) (t-var 'nemtpy))
 (eqc (t-var 'x) (t-list (t-var 'g139201)))
 (eqc (t-var 'g139202) (t-list (t-var 'g139201)))))
;; tempty?
((constraint-list=?
  (generate-constraints 'x (parse '(tempty? true))))
(list (eqc (t-var 'g140059) (t-bool)) 
      (eqc (t-var 'x) (t-bool)) 
      (eqc (t-var 'g140059) (t-list (t-var 'any)))))
;; tfirst
((constraint-list=? 
  (generate-constraints 'x (parse '(tfirst tempty))))
(list
 (eqc (t-var 'g130922) (t-list (t-var 'g130924)))
 (eqc (t-var 'x) (t-var 'g130923))
 (eqc (t-var 'g130922) (t-list (t-var 'g130923)))))
((constraint-list=? 
  (generate-constraints 'x (parse '(tfirst (tcons 4 tempty)))))
(list
 (eqc (t-var 'g131440) (t-num))
 (eqc (t-var 'g131441) (t-list (t-var 'g131442)))
 (eqc (t-var 'g131438) (t-list (t-var 'g131440)))
 (eqc (t-var 'g131441) (t-list (t-var 'g131440)))
 (eqc (t-var 'x) (t-var 'g131439))
 (eqc (t-var 'g131438) (t-list (t-var 'g131439)))))
;; trest
((constraint-list=?
  (generate-constraints 'x (parse '(trest tempty))))
(list
 (eqc (t-var 'g102415) (t-list (t-var 'g102417)))
 (eqc (t-var 'x) (t-list (t-var 'g102416)))
 (eqc (t-var 'g102415) (t-list (t-var 'g102416)))))
((constraint-list=? 
  (generate-constraints 'x (parse '(trest (tcons 1 tempty)))))
(list
 (eqc (t-var 'g132058) (t-num))
 (eqc (t-var 'g132059) (t-list (t-var 'g132060)))
 (eqc (t-var 'g132056) (t-list (t-var 'g132058)))
 (eqc (t-var 'g132059) (t-list (t-var 'g132058)))
 (eqc (t-var 'x) (t-list (t-var 'g132057)))
 (eqc (t-var 'g132056) (t-list (t-var 'g132057)))))

;; 3.19.5 Unification

(define (subst-type t old-id new-type)
  (type-case Type t
    [t-list (elem)
      (t-list (subst-type elem old-id new-type))]
    [t-fun (arg result)
      (t-fun (subst-type arg old-id new-type) (subst-type result old-id new-type))]
    [t-var (v)
      (if (eq? v old-id) new-type t)]
    [else t]))

(define (subst-const c old-id new-type)
  (type-case Constraint c
     [eqc (lhs rhs)
       (eqc
         (subst-type lhs old-id new-type)
         (subst-type rhs old-id new-type))]))

;; Purpose: Runs unification algorithm on a list of constraints
;; and determins if there is a type conflict
;; Contract: (unify loc) -> (listof Constraint?)
;;           loc : (listof Constraint?)
(define (unify loc [sub empty])
  (if (empty? loc)
    sub
    (type-case Constraint (first loc)
      [eqc (lhs rhs)
        (local [
            (define (unify-subst old new)
              (unify
                (map (λ (c) (subst-const c (t-var-v old) new)) (rest loc))
                (cons
                  (eqc old new)
                  (map (λ (c) (subst-const c (t-var-v old) new)) sub))))]
          (cond
            [(and (t-var? lhs) (t-var? rhs) (eq? (t-var-v lhs) (t-var-v rhs)))
              (unify (rest loc) sub)]
            [(t-var? lhs)
              (unify-subst lhs rhs)]
            [(t-var? rhs)
              (unify-subst rhs lhs)]
            [(and (t-num? lhs) (t-num? rhs))
              (unify (rest loc) sub)]
            [(and (t-bool? lhs) (t-bool? rhs))
              (unify (rest loc) sub)]
            [(and (t-list? lhs) (t-list? rhs)) 
              (unify
                (list* (eqc (t-list-elem lhs) (t-list-elem rhs)) (rest loc))
                sub)]
            [(and (t-fun? lhs) (t-fun? rhs))
              (unify
                (list*
                  (eqc (t-fun-arg lhs) (t-fun-arg rhs))
                  (eqc (t-fun-result lhs) (t-fun-result rhs))
                  (rest loc))
                sub)]
            [else
               (error "Inconsistent types: ~a and ~a"
                 (eqc-lhs (first loc)) (eqc-rhs (first loc)))]))])))


;; 3.19.6 Inferring Types

;; Purpose: Infers the type of the expression
;; Contract: (infer-type e) -> Type?
;;           e : Expr?
(define (infer-type e)
  (eqc-rhs
    (local ([define root-id (gensym)])
      (findf
        (λ (c) (eq? root-id (t-var-v (eqc-lhs c))))
        (unify (generate-constraints root-id (alpha-vary e)))))))

;; TESTS FOR INFERRING TYPES
(define (run sexp)
  (infer-type (parse sexp)))

(define (type-is sexp type)
  ((type=? (run sexp)) type))

;;num
(test (type-is '1 (t-num)) #t)
(test (type-is '1000000 (t-num)) #t)
(test (type-is '-1 (t-num)) #t)
(test (type-is '-1000000 (t-num)) #t)
  
;;true
(test (type-is 'true (t-bool)) #t)

;;false
(test (type-is 'false (t-bool)) #t)

;;plus
(test (type-is '(+ 1 1) (t-num)) #t)
(test (type-is '(+ (+ 1 1) 1) (t-num)) #t)
(test (type-is '(+ 1 (+ 1 1)) (t-num)) #t)
(test/exn (run '(+ 0 true)) "")
(test/exn (run '(+ false 0)) "")
(test/exn (run '(+ tempty 0)) "")
(test/exn (run '(+ 0 tempty)) "")
(test/exn (run '(+ (fun (a) true) 0)) "")

;;minus
(test (type-is '(- 1 1) (t-num)) #t)
(test (type-is '(- (+ 1 1) 1) (t-num)) #t)
(test (type-is '(- 1 (+ 1 1)) (t-num)) #t)
(test/exn (run '(- 0 true)) "")
(test/exn (run '(- false 0)) "")
(test/exn (run '(- tempty 0)) "")
(test/exn (run '(- 0 tempty)) "")
(test/exn (run '(- (fun (a) true) 0)) "")

;;multiply
(test (type-is '(* 1 1) (t-num)) #t)
(test (type-is '(* (+ 1 1) 1) (t-num)) #t)
(test (type-is '(* 1 (+ 1 1)) (t-num)) #t)
(test/exn (run '(* 0 true)) "")
(test/exn (run '(* false 0)) "")
(test/exn (run '(* tempty 0)) "")
(test/exn (run '(* 0 tempty)) "")
(test/exn (run '(* (fun (a) true) 0)) "")

;;iszero
(test (type-is '(iszero 1) (t-bool)) #t)
(test (type-is '(iszero 0) (t-bool)) #t)
(test (type-is '(iszero (tfirst tempty)) (t-bool)) #t)
(test (type-is '(iszero (tfirst (tcons 1 tempty))) (t-bool)) #t)
(test (type-is '(iszero ((fun (x) 0) true)) (t-bool)) #t) 
(test/exn (run '(iszero true)) "")
(test/exn (run '(iszero false)) "")
(test/exn (run '(iszero (tcons 1 1))) "")
(test/exn (run '(iszero (fun (x) 0))) "")

;; bif
(test (type-is '(bif true 1 1) (t-num)) #t)
(test/exn (run '(bif true 1 true)) "")
(test/exn (run '(bif true true 1)) "")
(test/exn (run '(bif 1 1 1)) "")
(test (type-is '(bif (bif true true false) 1 1) (t-num)) #t)
(test (type-is '(bif true (bif true 1 1) 1) (t-num)) #t)
(test (type-is '(bif true 1 (bif true 1 1)) (t-num)) #t)
(test (run '(bif true (+ 1 1) (+ 1 1))) (t-num))
(test (run '(bif true true true)) (t-bool))
(test (run '(bif true true true)) (t-bool))

;; tempty & tcons
(test (type-is 'tempty (t-list (t-var (gensym)))) #t)

(test (type-is '(tcons 1 tempty) (t-list (t-num))) #t)
(test (type-is '(tcons true tempty) (t-list (t-bool))) #t)
(test (type-is '(tcons (fun (x) 1) tempty) 
               (t-list (t-fun (t-var (gensym)) (t-num)))) #t)
(test (type-is '(tcons (fun (x) true) tempty) 
               (t-list (t-fun (t-var (gensym)) (t-bool)))) #t)
(test (type-is '(tcons 1 (tcons 1 tempty)) (t-list (t-num))) #t)
(test (type-is '(tcons (tcons 1 tempty) tempty) (t-list (t-list (t-num)))) #t)
(test (type-is '(tcons (+ 1 1) tempty) (t-list (t-num))) #t)
(test/exn (run '(tcons ((fun (x) x) 1) nempty)) "")
(test (type-is '(tcons true tempty) (t-list (t-bool))) #t)

(test/exn (run '(tcons 1 1)) "")
(test/exn (run '(tcons tempty 1)) "")
(test/exn (run '(tcons 1 true)) "")

;; tempty?
(test (run '(tempty? tempty)) (t-bool))
(test (run '(tempty? (tcons 1 tempty))) (t-bool))
(test/exn (run '(tempty? 0)) "")
(test/exn (run '(tempty? true)) "")
(test/exn (run '(tempty? (fun (x) 1))) "")

;; tfirst & trest
(test (type-is '(tfirst tempty) (t-var (gensym))) #t)
(test (run '(tfirst (tcons 1 tempty))) (t-num))
(test (type-is '(tfirst (tcons true tempty)) (t-bool)) #t)
(test (type-is '(tfirst (tcons (fun (x) 1) tempty)) 
      (t-fun (t-var (gensym)) (t-num))) #t)
(test/exn (run '(tfirst 1)) "")
(test/exn (run '(tfirst true)) "")
(test/exn (run '(tfirst false)) "")
(test/exn (run '(tfirst (+ 1 1))) "")
(test/exn (run '(tfirst (fun (x) 1))) "")

(test (type-is '(trest tempty) (t-list(t-var (gensym)))) #t)
(test (type-is '(trest (tcons 1 tempty)) (t-list (t-num))) #t)
(test (type-is '(trest (tcons (fun (x) 1) tempty)) 
               (t-list (t-fun (t-var (gensym)) (t-num)))) #t)
(test (type-is '(trest (tcons true tempty)) (t-list (t-bool))) #t)
(test/exn (run '(trest (tcons true (tcons 1 tempty)))) "")
(test/exn (run '(trest 1)) "")
(test/exn (run '(trest true)) "")
(test/exn (run '(trest false)) "")
(test/exn (run '(trest (+ 1 1))) "")
(test/exn (run '(trest (fun (x) 1))) "")

;; fun & app
(test/exn (run '(fun (x) t x)) "")
(test/exn (type-is '(fun (y)  y)
                   (t-fun (t-var (gensym)) (t-var (gensym)))) "")

(test (type-is '(fun (x) (+ x 1)) (t-fun (t-num) (t-num))) #t)
(test (type-is '(fun (x) true) (t-fun (t-var (gensym)) (t-bool))) #t)
(test (type-is '(+ 1 ((fun (x) 1) 1)) (t-num)) #t)
(test (type-is '((fun (x) tempty) 1) (t-list (t-var (gensym)))) #t)
(test (type-is '((fun (x) tempty) true) (t-list (t-var (gensym)))) #t)

;; with
(test (type-is '(with (x 1) x) (t-var (gensym))) #t)
(test (type-is '(with (x 1) 1) (t-num)) #t)
(test (type-is '(with (x true) (bif x false x)) (t-bool)) #t)
(test (type-is '(with (x 1) (+ 1 x)) (t-num)) #t)
(test (type-is '(with (x (fun (y) (* y y))) (x 2)) (t-var (gensym))) #t)
(test (type-is '(with (x 1) (with (y 2) (+ x y))) (t-num)) #t)
(test (type-is '(with (x 1) (with (y true) (+ x y))) (t-num)) #t)
(test (type-is '(with (x true) (with (y 1) (+ x y))) (t-num)) #t)
(test (type-is '(with (x true) (with (y 1) (bif x y x))) (t-bool)) #t)
(test (run '(with (x true) (with (y 1) (bif x y (+ y 1))))) (t-num))


;; rec-with
(test (type-is '(rec (x 1) x) (t-var (gensym))) #t)
(test (type-is '(rec (x 1) 1) (t-num)) #t)
(test (type-is '(rec (x true) (bif x false x)) (t-bool)) #t)
(test (type-is '(rec (x 1) (+ 1 x)) (t-num)) #t)
(test (type-is '(rec (x (fun (y) (* y y))) (x 2)) (t-var (gensym))) #t)
(test (type-is '(rec (x 1) (with (y 2) (+ x y))) (t-num)) #t)
(test (type-is '(rec (x 1) (with (y true) (+ x y))) (t-num)) #t)
(test (type-is '(rec (x true) (with (y 1) (+ x y))) (t-num)) #t)
(test (type-is '(rec (x true) (with (y 1) (bif x y x))) (t-bool)) #t)
(test (run '(rec (x true) (with (y 1) (bif x y (+ y 1))))) (t-num))


;; with errors
;(test/exn (run '(with (1 x) 1)) "")
(test/exn (run '(with (x 1) y)) "")
(test/exn (run '(with (x 1) 'hi)) "")

;; rec errors
;(test/exn (run '(rec (1 x) 1)) "")
(test/exn (run '(rec (x 1) y)) "")
(test/exn (run '(rec (x 1) 'hi)) "")


;;fun
(test (type-is '(fun (x) 0) (t-fun (t-var 'a) (t-num))) #t)
(test (type-is
  '(fun (x) ((fun (x) (+ x 1)) (bif x 1 0)))
  (t-fun (t-bool) (t-num))) #t)

;;EXTRA CREDIT
(test (type-is '(fun (x) (tfirst tempty)) (t-fun (t-var 'a) (t-var 'b))) #t)

