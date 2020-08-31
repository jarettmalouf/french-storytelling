#lang racket

(provide concat concat? concat-arg1 concat-arg2
         either either? either-arg1 either-arg2
         repeat repeat? repeat-arg1
         ok-string? reg-exp?
         flip pick
         generate-string-from-reg-exp
         dfa dfa? dfa-alphabet dfa-states dfa-start-state dfa-accepting-states dfa-transitions
         entry entry? entry-key entry-value
         dfa-accepts?
         cfg cfg? cfg-terminals cfg-nonterminals cfg-start-symbol cfg-rules
         rule rule? rule-lhs rule-rhs
         leaf leaf? leaf-label
         node node? node-label node-children
         list-leaf-labels
         generate-parse-tree-from-cfg generate-string-from-cfg
         dfa-mcd
         exp-mcd
         my-cfg)

; returns the symbols in a list
(define (list-of-symbols? lst)
  (cond
    [(empty? lst) #t]
    [(symbol? (car lst)) (list-of-symbols? (cdr lst))]
    [else #f]))

; returns #t if the value satisfies the aforementioned conditions
(define (ok-string? value)
  (cond
    [(empty? value) #t]
    [(or (not (list? value)) (not (symbol? (car value)))) #f]
    [(symbol? (car value)) (ok-string? (cdr value))]))

; returns #t if every part of value is an ok-string
(define (reg-exp? value)
  (cond
    [(ok-string? value) #t]
    [(concat? value) (and (reg-exp? (concat-arg1 value))
                          (reg-exp? (concat-arg2 value)))]
    [(either? value) (and (reg-exp? (either-arg1 value))
                          (reg-exp? (either-arg2 value)))]
    [(repeat? value) (reg-exp? (repeat-arg1 value))]
    [else #f]))

; produces random number between 0 and 1, and compares it to bias
(define (flip bias)
  (<= (random) bias))

; gets an item in position pos in a list
(define (get pos lst)
  (cond
    [(> pos (length lst)) empty] [(equal? 0 pos) (car lst)]
    [(> pos 0) (get (- pos 1) (cdr lst))]))

; randomly chooses an item in a list
(define (pick lst)
  (if (empty? lst) #f (get (random (length lst)) lst)))

; uses probability to randomly generate a string from a regular expression
(define (generate-string-from-reg-exp exp)
  (cond
    [(empty? exp)  exp]
    [(concat? exp) (append (generate-string-from-reg-exp (concat-arg1 exp))
                           (generate-string-from-reg-exp (concat-arg2 exp)))]
    [(and (either? exp) (flip .5)) (generate-string-from-reg-exp (either-arg1 exp))]
    [(either? exp) (generate-string-from-reg-exp (either-arg2 exp))]
    [(and (repeat? exp) (flip .5)) (append (generate-string-from-reg-exp (repeat-arg1 exp))
                                           (generate-string-from-reg-exp exp))]
    [(repeat? exp) '()]
    [(list-of-symbols? exp) exp]))

(define (is-in? item lst)
  (cond
    [(empty? lst) #f] [(equal? item (car lst)) #t] [else (is-in? item (cdr lst))]))

; returns the transitions in the form of a list '((even a) (even b) ...
(define (list-transitions transitions)
  (if (empty? transitions) empty
      (cons (entry-key (car transitions)) (list-transitions (cdr transitions)))))

; finds the corresponding instruction to a transition
; i.e. '(even a) 'odd --> 'odd
(define (find-ins state transitions letter)
  (cond
    [(not (is-in? (append (list state) (list letter)) (list-transitions transitions))) #f]
    [(equal? (append (list state) (list letter))
              (entry-key (car transitions))) (entry-value (car transitions))]
    [else (find-ins state (cdr transitions) letter)]))

; generates the next configuration of the machine after 1 step
(define (next-step mach str)
  (if (not (find-ins (dfa-start-state mach) (dfa-transitions mach) (car str))) #f
    (dfa
     (dfa-alphabet mach)
     (dfa-states mach)
     (find-ins (dfa-start-state mach) (dfa-transitions mach) (car str))
     (dfa-accepting-states mach)
     (dfa-transitions mach))))

; goes through all the steps until the machine halts
; then checks whether or not the current state is in the accepted states
(define (dfa-accepts? mach str)
  (cond
    [(empty? str) (is-in? (dfa-start-state mach) (dfa-accepting-states mach))]
    [(not (next-step mach str)) #f]
    [else (dfa-accepts? (next-step mach str) (cdr str))]))
    
; produces a list of the leaf labels
(define (list-leaf-labels-aux tree)
  (cond
    [(node? tree) (map list-leaf-labels-aux (node-children tree))]
    [(leaf? tree) (leaf-label tree)]))

; removes auxiliary function's internal parentheses
(define (list-leaf-labels tree)
  (flatten (list-leaf-labels-aux tree)))

; given 's, returns all the rules with the key 's
(define (get-keyed-rules start rules)
  (cond
    [(empty? rules) empty]
    [(equal? start (rule-lhs (car rules))) (cons (car rules) (get-keyed-rules start (cdr rules)))]
    [else (get-keyed-rules start (cdr rules))]))

; given 's, picks a random rule with the key 's, e.g. (rule 's '(np vp))
(define (get-rand-rule start rules)
  (pick (get-keyed-rules start rules)))

; takes a grammar and a list of new-heads, e.g. '(np vp)
; and returns (length (new-heads)) new cfgs [in this case, 2]
; each with a new start-symbol of one of the elements of new-heads
(define (make-list-of-cfgs grammar new-heads)
  (cond
    [(empty? new-heads) empty]
    [(cons (cfg
            (cfg-terminals grammar)
            (cfg-nonterminals grammar)
            (car new-heads)
            (cfg-rules grammar))
           (make-list-of-cfgs grammar (cdr new-heads)))]))
                        
; if it's a terminal element, return the leaf
; if it's a nonterminal element, return a node with the start-symbol as its label
; and a mapped recursive call to the new cfg's created by make-list-of-cfgs as its children
(define (generate-parse-tree-from-cfg grammar)
  (cond
    [(is-in? (cfg-start-symbol grammar) (cfg-terminals grammar)) (leaf (cfg-start-symbol grammar))]
    [else (node (cfg-start-symbol grammar)
                (map generate-parse-tree-from-cfg
                     (make-list-of-cfgs grammar
                     (rule-rhs (get-rand-rule (cfg-start-symbol grammar) (cfg-rules grammar))))))]))

(define (gen-string-from-tree tree)
  (cond
    [(leaf? tree) tree]
    [else (map gen-string-from-tree (node-children tree))]))

(define (flat-string leaf-lst)
  (if (empty? leaf-lst) empty (cons (leaf-label (car leaf-lst)) (flat-string (cdr leaf-lst)))))

(define (generate-string-from-cfg grammar)
  (flat-string (flatten (gen-string-from-tree (generate-parse-tree-from-cfg grammar)))))

; recognize the language of the CFG grammar-mcd.
(define dfa-mcd
  (dfa
    (cfg-terminals grammar-mcd)
    '(det n vp np f rel np2)
    'det
    '(f)
    (list
     (entry '(det a) 'n)
     (entry '(det the) 'n)
     (entry '(det it) 'vp)
     (entry '(n mouse) 'vp)
     (entry '(n cat) 'vp)
     (entry '(n dog) 'vp)
     (entry '(vp chased) 'np)
     (entry '(vp evaded) 'np)
     (entry '(vp slept) 'f)
     (entry '(vp swam) 'f)
     (entry '(vp dreamed) 'rel)
     (entry '(vp believed) 'rel)
     (entry '(np a) 'np2)
     (entry '(np the) 'np2)
     (entry '(np it) 'f)
     (entry '(np2 mouse) 'f)
     (entry '(np2 cat) 'f)
     (entry '(np2 dog) 'f)
     (entry '(rel that) 'det))))
  


; Regular Expression named exp-mcd to denote the language of 
; the CFG grammar-mcd.
(define exp-mcd
  (concat
   (repeat
    (concat (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it))
              (concat (either '(believed) '(dreamed)) '(that))))
   (concat
    (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it))
      (either (either '(slept) '(swam)) (concat (either '(chased) '(evaded))
                                              (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it)))))))

; np: (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it))
; vp: (either (either '(slept) '(swam)) (concat (either '(chased) '(evaded))
;                                             (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it))))

; my-cfg defines a French grammar that tells the story
; of a character who possesses or does not possess information
; about other character(s) who feel(s) a certain way about other character(s),
; who is/are socially or familially related to other character(s)

; my-cfg takes into account the gendered nature of French
; e.g. its gendered articles (le / la / l'),
; its gendered partitives (du / de la / de l')
; and gendered compositions of past participles (était tombé amoureux / était tombée amoureuse)
; note 1: because l' is not a symbol, l' has been replaced with l- (l'homme --> l- homme)
; note 2: the only l' nouns in this grammar are masculine

; here are some examples of strings generated by my-cfg,
; followed by an English translation

; (generate-string-from-cfg my-cfg)

; > (la fille avait peur de la cousine)
; >> the girl was afraid of the [female] cousin

; > (l- homme était tombé amoureux du professeur)
; >> the man had fallen in love with the [male] professor

; > (l- enfant a su que la fille était tombée amoureuse du cousin de l- homme)
; >> the child knew that the girl had fallen in love with the man's [male] cousin

; > (l- enfant n-a pas appris que le cousin avait peur du cousin du garçon)
; >> the child did not learn that the [male] cousin was afraid of the boy's [male] cousin

; > (la femme a su que la fille a compris que le cousin avait envie de l- homme de la femme du professeur)
; >> the woman knew that the girl understood that the [male] cousin was jealous of the husband of the [male] professor's wife

(define my-cfg
  (cfg
   '(le la l- cousin garçon professeur homme enfant fille femme cousine n-a pas a su vu compris appris que était avait
        tombé amoureux tombée amoureuse peur envie de du)
   '(s np vp npf dm nm df nf dl nl vp vpf vpa vpaf io pc0 pc1 pc2 pc3 pcv neg rel epm epf adjm adjf n al af pm pfl dom dof dol)
   's
   (list
    (rule 's '(np vp))
    (rule 's '(npf vpf))
    (rule 'np '(dm nm))
    (rule 'npf '(df nf))
    (rule 'np '(dl nl))
    (rule 'dm '(le))
    (rule 'df '(la))
    (rule 'dl '(l-))
    (rule 'nm '(cousin))
    (rule 'nm '(garçon))
    (rule 'nm '(professeur))
    (rule 'nf '(fille))
    (rule 'nf '(femme))
    (rule 'nf '(cousine))
    (rule 'nl '(homme))
    (rule 'nl '(enfant))
    (rule 'vp '(vpa io))
    (rule 'vpf '(vpaf io))
    (rule 'vpa '(pc0 pcv que s))
    (rule 'vpa '(pc1 neg pcv que s))
    (rule 'vpa '(pc0 pcv que s))
    (rule 'vpa '(pc1 neg pcv que s))
    (rule 'vpaf '(pc0 pcv que s))
    (rule 'vpaf '(pc1 neg pcv que s))
    (rule 'vpaf '(pc0 pcv que s))
    (rule 'vpaf '(pc1 neg pcv que s))
    (rule 'vpa '(pc2 epm adjm))
    (rule 'vpaf '(pc2 epf adjf))
    (rule 'vpa '(pc3 n))
    (rule 'vpaf '(pc3 n))
    (rule 'io '(pm dom))
    (rule 'io '(pfl af dof))
    (rule 'io '(pfl al dol))
    (rule 'pc0 '(a))
    (rule 'pc1 '(n-a))
    (rule 'neg '(pas))
    (rule 'pcv '(su))
    (rule 'pcv '(vu))
    (rule 'pcv '(compris))
    (rule 'pcv '(appris))
    (rule 'pc2 '(était))
    (rule 'pc3 '(avait))
    (rule 'n '(envie))
    (rule 'n '(peur))
    (rule 'epm '(tombé))
    (rule 'epf '(tombée))
    (rule 'adjm '(amoureux))
    (rule 'adjf '(amoureuse))
    (rule 'pm '(du))
    (rule 'pfl '(de))
    (rule 'af '(la))
    (rule 'al '(l-))
    (rule 'dof '(fille))
    (rule 'dof '(femme))
    (rule 'dof '(cousine))
    (rule 'dom '(cousin))
    (rule 'dom '(garçon))
    (rule 'dom '(professeur))
    (rule 'dol '(homme))
    (rule 'dol '(enfant)))))
