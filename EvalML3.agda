
module EvalML3 where

open import Data.Nat using (ℕ; suc; compare; equal)
open import Data.Integer
  hiding (suc; -_)
  renaming (_+_ to _ℤ+_; _-_ to _ℤ-_; _*_ to _ℤ*_)
open import Data.Bool hiding (if_then_else_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List -- renaming ([] to •) -- \bub
open import Data.Product using (_×_; _,_)

-- declarations
data Val : Set
data Var : Set
Env : Set
data Exp : Set

-- value
data Val where
  int        : ℤ → Val
  bool       : Bool → Val
  -- closure
  [_][fun_=>_] : Env → Var → Exp → Val
  -- closure of a recusive function
  [_][rec_be:fun_=>_] : Env → Var → Var → Exp → Val

-- variable
data Var where
  id : ℕ → Var

-- environment
Env = List (Var × Val)

-- syntax
data Exp where
  VAL  : Val → Exp
  VAR  : Var → Exp
  _+_  : Exp → Exp → Exp
  _-_  : Exp → Exp → Exp
  _*_  : Exp → Exp → Exp
  _<_  : Exp → Exp → Exp
  _⊳_  : Exp → Exp → Exp -- application
  IF_THEN_ELSE_ : Exp → Exp → Exp → Exp
  LET_BE_IN_    : Var → Exp → Exp → Exp
  FUN_=>_       : Var → Exp → Exp
  LETREC_BE:FUN_=>_IN_ : Var → Var → Exp → Exp → Exp

infixl 30 _⊳_
infixl 20 _*_
infixl 10 _+_ _-_
infix   5 _<_
infix   3 FUN_=>_
infix   2 IF_THEN_ELSE_
infix   1 LET_BE_IN_ LETREC_BE:FUN_=>_IN_
infix   0 _⊢_⇓_

-- utilities
ip : ℕ → Val -- integer plus value
ip n = int (+ n)
-_ : ℕ → ℤ
- n = -[1+ n ] ℤ+ (+ 1)
im : ℕ → Val -- integer minus value
im n = int (- n)

X = id 0
Y = id 1

X≢Y : X ≢ Y
X≢Y ()

-- auxiliary functions
_ℕ<_ : ℕ → ℕ → Bool
_ ℕ< 0 = false
0 ℕ< (suc _) = true
(suc n) ℕ< (suc m) = n ℕ< m

_ℤ<_ : ℤ → ℤ → Bool
(+    x) ℤ<    (+ y) = x ℕ< y
-[1+ x ] ℤ<    (+ y) = true
(+    x) ℤ< -[1+ y ] = false
-[1+ x ] ℤ< -[1+ y ] = y ℕ< x

-- inference rules
data _⊢_⇓_ : Env → Exp → Val → Set where

  e-int   : ∀ {Ε i} → Ε ⊢ (VAL (int i)) ⇓ (int i)

  e-bool  : ∀ {Ε b} → Ε ⊢ (VAL (bool b)) ⇓ (bool b)

  e-var₁  : ∀ {Ε x v} → (x , v) ∷ Ε ⊢ (VAR x) ⇓ v

  e-var₂  : ∀ {Ε x y v₁ v₂} → {neq : x ≢ y} →
            Ε ⊢ (VAR x) ⇓ v₂ → (y , v₁) ∷ Ε ⊢ (VAR x) ⇓ v₂

  e-ift   : ∀ {Ε e₁ e₂ e₃ v} →
            Ε ⊢ e₁ ⇓ (bool true) →
            Ε ⊢ e₂ ⇓ v →
            Ε ⊢ IF e₁ THEN e₂ ELSE e₃ ⇓ v

  e-iff   : ∀ {Ε e₁ e₂ e₃ v} →
            Ε ⊢ e₁ ⇓ (bool false) →
            Ε ⊢ e₃ ⇓ v →
            Ε ⊢ IF e₁ THEN e₂ ELSE e₃ ⇓ v

  e-plus  : ∀ {Ε e₁ e₂ i₁ i₂ i₃} →
            Ε ⊢ e₁ ⇓ (int i₁) →
            Ε ⊢ e₂ ⇓ (int i₂) →
            i₁ ℤ+ i₂ ≡ i₃ →
            Ε ⊢ e₁ + e₂ ⇓ (int i₃)

  e-minus : ∀ {Ε e₁ e₂ i₁ i₂ i₃} →
            Ε ⊢ e₁ ⇓ (int i₁) →
            Ε ⊢ e₂ ⇓ (int i₂) →
            i₁ ℤ- i₂ ≡ i₃ →
            Ε ⊢ e₁ - e₂ ⇓ (int i₃)

  e-times : ∀ {Ε e₁ e₂ i₁ i₂ i₃} →
            Ε ⊢ e₁ ⇓ (int i₁) →
            Ε ⊢ e₂ ⇓ (int i₂) →
            i₁ ℤ* i₂ ≡ i₃ →
            Ε ⊢ e₁ * e₂ ⇓ (int i₃)

  e-lt    : ∀ {Ε e₁ e₂ i₁ i₂ b} →
            Ε ⊢ e₁ ⇓ (int i₁) →
            Ε ⊢ e₂ ⇓ (int i₂) →
            i₁ ℤ< i₂ ≡ b →
            Ε ⊢ e₁ < e₂ ⇓ (bool b)

  e-let   : ∀ {Ε e₁ e₂ x v v₁} → 
            Ε ⊢ e₁ ⇓ v₁ →
            (x , v₁) ∷ Ε ⊢ e₂ ⇓ v →
            Ε ⊢ LET x BE e₁ IN e₂ ⇓ v

  -- newcomers in EvalML3
  e-fun   : ∀ {Ε e x} → Ε ⊢ FUN x => e ⇓ [ Ε ][fun x => e ]

  e-app   : ∀ {Ε Ε₂ e₀ e₁ e₂ x v v₂} →
            Ε ⊢ e₁ ⇓ [ Ε₂ ][fun x => e₀ ] →
            Ε ⊢ e₂ ⇓ v₂ →
            (x , v₂) ∷ Ε₂ ⊢ e₀ ⇓ v →
            Ε ⊢ e₁ ⊳ e₂ ⇓ v

  e-letrec : ∀ {Ε e₁ e₂ x y v} →
             (x , [ Ε ][rec x be:fun y => e₁ ]) ∷ Ε ⊢ e₂ ⇓ v →
             Ε ⊢ LETREC x BE:FUN y => e₁ IN e₂ ⇓ v

  e-apprec : ∀ {Ε Ε₂ e₀ e₁ e₂ x y v v₂} →
             Ε ⊢ e₁ ⇓ [ Ε₂ ][rec x be:fun y => e₀ ] →
             Ε ⊢ e₂ ⇓ v₂ →
             (y , v₂) ∷ (x , [ Ε₂ ][rec x be:fun y => e₀ ]) ∷ Ε₂ ⊢ e₀ ⇓ v →
             Ε ⊢ e₁ ⊳ e₂ ⇓ v

-- exercises

-- Problem 41 (from http://www.fos.kuis.kyoto-u.ac.jp/~igarashi/CoPL/index.cgi)
ex41 : [] ⊢ LET Y BE (VAL (ip 2)) IN FUN X => (VAR X) + (VAR Y) ⇓
       [ (Y , (ip 2)) ∷ [] ][fun X => (VAR X) + (VAR Y) ]
ex41 = e-let e-int e-fun

TWICE = id 2
F = id 3

ex5-1-3 : [] ⊢ LET TWICE BE FUN F => FUN X => (VAR F) ⊳ ((VAR F) ⊳ (VAR X))
               IN (VAR TWICE) ⊳ (VAR TWICE) ⊳ (FUN X => (VAR X) * (VAR X)) ⊳ (VAL (ip 2))
          ⇓ (ip 65536)
ex5-1-3 = e-let e-fun (e-app (e-app (e-app e-var₁ e-var₁ e-fun)
                                    e-fun
                                    (e-app (e-var₂ {neq = λ ()} e-var₁)
                                           (e-app (e-var₂ {neq = λ ()} e-var₁) e-var₁ e-fun)
                                           e-fun))
                             e-int
                             (e-app (e-var₂ {neq = λ ()} e-var₁)
                                    (e-app (e-var₂ {neq = λ ()} e-var₁)
                                           e-var₁
                                           (e-app (e-var₂ {neq = λ ()} e-var₁)
                                                  (e-app (e-var₂ {neq = λ ()} e-var₁)
                                                         e-var₁
                                                         (e-times e-var₁ e-var₁ refl))
                                                  (e-times e-var₁ e-var₁ refl)))
                                    (e-app (e-var₂ {neq = λ ()} e-var₁)
                                           (e-app (e-var₂ {neq = λ ()} e-var₁)
                                                  e-var₁
                                                  (e-times e-var₁ e-var₁ refl))
                                           (e-times e-var₁ e-var₁ refl))))

SUM = id 4
N = id 5

ex5-1-6 : [] ⊢ LETREC SUM BE:FUN F => FUN N =>
                      (IF (VAR N) < (VAL (ip 1)) THEN (VAL (ip 0))
                      ELSE (VAR F) ⊳ (VAR N) + (VAR SUM) ⊳ (VAR F) ⊳ ((VAR N) - (VAL (ip 1))))
               IN
               (VAR SUM) ⊳ (FUN X => (VAR X) * (VAR X)) ⊳ (VAL (ip 2))
          ⇓ (ip 5)
ex5-1-6 = e-letrec (e-app (e-apprec e-var₁ e-fun e-fun)
                          e-int
                          (e-iff (e-lt e-var₁ e-int refl)
                                 (e-plus (e-app (e-var₂ {neq = λ ()} e-var₁)
                                                e-var₁
                                                (e-times e-var₁ e-var₁ refl))
                                         (e-app (e-apprec (e-var₂ {neq = λ ()} (e-var₂ {neq = λ ()} e-var₁))
                                                          (e-var₂ {neq = λ ()} e-var₁)
                                                          e-fun)
                                                (e-minus e-var₁ e-int refl)
                                                (e-iff (e-lt e-var₁ e-int refl)
                                                       (e-plus (e-app (e-var₂ {neq = λ ()} e-var₁)
                                                                      e-var₁
                                                                      (e-times e-var₁ e-var₁ refl))
                                                               (e-app (e-apprec (e-var₂ {neq = λ ()} (e-var₂ {neq = λ ()} e-var₁))
                                                                                (e-var₂ {neq = λ ()} e-var₁)
                                                                                e-fun)
                                                                      (e-minus e-var₁ e-int refl)
                                                                      (e-ift (e-lt e-var₁ e-int refl)
                                                                             e-int))
                                                               refl)))
                                         refl)))

raw : {x y : ℤ} → int x ≡ int y → x ≡ y
raw refl = refl

-- handy version of congrous
congw : {A : Set} → {b c : A} → {cons : A → Val} → b ≡ c → cons b ≡ cons c
congw refl = refl

unique : {A B C : Set} → {a a' : A} → {b b' : B} → {c c' : C} →
                (_⋆_ : A → B → C) →
                a ≡ a' → b ≡ b' → a ⋆ b ≡ c → a' ⋆ b' ≡ c' → c ≡ c'
unique {a = a} {a' = a'} {b = b} {b' = b'} {c = c} {c' = c'} _⋆_ a≡a' b≡b' eq eq' = begin
  c ≡⟨ sym eq ⟩
  a  ⋆ b  ≡⟨ cong (λ x → x  ⋆ b) a≡a' ⟩
  a' ⋆ b  ≡⟨ cong (λ x → a' ⋆ x) b≡b' ⟩
  a' ⋆ b' ≡⟨ eq' ⟩
  c' ∎

lem4-2 : {x : Var} → ∀ {Ε} → ∀ {v v'} → Ε ⊢ (VAR x) ⇓ v → Ε ⊢ (VAR x) ⇓ v' → v ≡ v'
lem4-2 e-var₁ e-var₁ = refl
lem4-2 (e-var₂ d) (e-var₂ d') = lem4-2 d d'
lem4-2 e-var₁ (e-var₂ {neq = neq} d) with neq refl -- neq refl : ⊥ because neq : x ≡ x → ⊥ and refl : x ≡ x
... | () -- there are no inhabitants in ⊥
lem4-2 (e-var₂ {neq = neq} d) e-var₁ with neq refl
... | ()


-- eval uniqueness
thm5-2 : ∀ {Ε} → ∀ {v v'} → (e : Exp) → Ε ⊢ e ⇓ v → Ε ⊢ e ⇓ v' → v ≡ v'

thm5-2 (VAL (int i)) e-int e-int = refl
thm5-2 (VAL (bool b)) e-bool e-bool = refl
thm5-2 (e₁ + e₂) (e-plus d d' eq) (e-plus f f' eq') =
         congw (unique _ℤ+_ (raw (thm5-2 e₁ d f))
                                     (raw (thm5-2 e₂ d' f'))
                                     eq eq')
thm5-2 (e₁ - e₂) (e-minus d d' eq) (e-minus f f' eq') =
         congw (unique _ℤ-_ (raw (thm5-2 e₁ d f))
                                     (raw (thm5-2 e₂ d' f'))
                                     eq eq')
thm5-2 (e₁ * e₂) (e-times d d' eq) (e-times f f' eq') =
         congw (unique _ℤ*_ (raw (thm5-2 e₁ d f))
                                     (raw (thm5-2 e₂ d' f'))
                                     eq eq')
thm5-2 (e₁ < e₂) (e-lt d d' eq) (e-lt f f' eq') =
         congw (unique _ℤ<_ (raw (thm5-2 e₁ d f))
                                     (raw (thm5-2 e₂ d' f'))
                                     eq eq')
thm5-2 (IF e₁ THEN e₂ ELSE e₃) (e-ift _ f) (e-ift _ f') = thm5-2 e₂ f f'
thm5-2 (IF e₁ THEN e₂ ELSE e₃) (e-iff _ f) (e-iff _ f') = thm5-2 e₃ f f'
thm5-2 (IF e THEN _ ELSE _) (e-iff d _) (e-ift d' _) with thm5-2 e d d'
... | ()
thm5-2 (IF e THEN _ ELSE _) (e-ift d _) (e-iff d' _) with thm5-2 e d d'
... | ()

thm5-2 (VAR x) d d' = lem4-2 d d'
thm5-2 (LET x BE e₁ IN e₂) (e-let d f) (e-let d' f') with thm5-2 e₁ d d'
thm5-2 (LET x BE e₁ IN e₂) (e-let d f) (e-let d' f') | refl = thm5-2 e₂ f f'

-- new in EvalML3
thm5-2 (FUN x => e) e-fun e-fun = refl

thm5-2 (e₁ ⊳ e₂) (e-app d f _) (e-app d' f' _) with thm5-2 e₁ d d' | thm5-2 e₂ f f'
thm5-2 (_ ⊳ _) (e-app {e₀ = e₀} _ _ g) (e-app _ _ g') | refl | refl = thm5-2 e₀ g g'

thm5-2 (LETREC x BE:FUN y => e₁ IN e₂) (e-letrec d) (e-letrec d') = thm5-2 e₂ d d'

thm5-2 (e₁ ⊳ e₂) (e-apprec d f g) (e-apprec d' f' g') with thm5-2 e₁ d d' | thm5-2 e₂ f f'
thm5-2 (_ ⊳ _) (e-apprec {e₀ = e₀} _ _ g) (e-apprec _ _ g') | refl | refl = thm5-2 e₀ g g'

thm5-2 (e₁ ⊳ e₂) (e-apprec d _ _) (e-app d' _ _) with thm5-2 e₁ d d'
... | ()
thm5-2 (e₁ ⊳ e₂) (e-app d _ _) (e-apprec d' _ _) with thm5-2 e₁ d d'
... | ()

