#lang plai

(print-only-errors #t)

(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)])
 
(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])

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

(define (eqSymbol? x sexp)
  (and (symbol? (first sexp)) (symbol=? x (first sexp))))

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
          (error "Parse: expected expr syntax"))]
    ))

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

;; fun
(test (parse '(fun (hi) 5)) 
      (fun 'hi (num 5)))
;(test (parse '(fun (x) (+ x 5))) 
      ;(fun 'x (bin-num-op 'x (id 'x) (num 5))))

;; rec 
(test (parse '(rec (hi 2) 5)) (rec-with 'hi (num 2) (num 5)))

;; app
(test (parse '(5 5)) (app (num 5) (num 5)))

;; tempty
(test (parse 'tempty) (tempty))

;; tcons
(test (parse '(tcons 5 5)) (tcons (num 5) (num 5)))

;; tempty?
(test (parse '(tempty? 5)) (istempty (num 5)))

;; tfirst 
(test (parse '(tfirst 5)) (tfirst (num 5)))

;; trest
(test (parse '(trest 5)) (trest (num 5)))