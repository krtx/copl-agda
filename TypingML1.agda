
module TypingML1 where

open import Data.Nat using (ℕ; suc)
open import Data.Integer
  hiding (suc; -_)
  renaming (_+_ to _ℤ+_; _-_ to _ℤ-_; _*_ to _ℤ*_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Sum
open import Data.Product using (∃; _,_; _×_)
open import Data.List

data Val : Set where
  int  : ℤ → Val
  bool : Bool → Val

data Res : Set where
  error : Res
  value : Val → Res

data Type : Set where
  int  : Type
  bool : Type

infixl 20 _*_
infixl 10 _+_ _-_
infix   5 _<_
infix   2 IF_THEN_ELSE_
infix   0 _⇓_ _∶_

-- Syntax.
data Exp : Set where
  VAL : Val → Exp
  _+_ : Exp → Exp → Exp
  _-_ : Exp → Exp → Exp
  _*_ : Exp → Exp → Exp
  _<_ : Exp → Exp → Exp
  IF_THEN_ELSE_ : Exp → Exp → Exp → Exp

-- Auxiliary functions.
_ℕ<_ : ℕ → ℕ → Bool
_ ℕ< 0 = false
0 ℕ< (suc _) = true
(suc n) ℕ< (suc m) = n ℕ< m

_ℤ<_ : ℤ → ℤ → Bool
(+    x) ℤ<    (+ y) = x ℕ< y
-[1+ x ] ℤ<    (+ y) = true
(+    x) ℤ< -[1+ y ] = false
-[1+ x ] ℤ< -[1+ y ] = y ℕ< x

-- Inference rules.
data _⇓_ : Exp → Res → Set where

  e-int   : ∀ {i} → (VAL (int i)) ⇓ value (int i)

  e-bool  : ∀ {b} → (VAL (bool b)) ⇓ value (bool b)

  e-ift   : ∀ {e₁ e₂ e₃ v} →
            e₁ ⇓ value (bool true) →
            e₂ ⇓ value v →
            IF e₁ THEN e₂ ELSE e₃ ⇓ value v

  e-iff   : ∀ {e₁ e₂ e₃ v} →
            e₁ ⇓ value (bool false) →
            e₃ ⇓ value v →
            IF e₁ THEN e₂ ELSE e₃ ⇓ value v

  e-plus  : ∀ {e₁ e₂ i₁ i₂ i₃} →
            e₁ ⇓ value (int i₁) →
            e₂ ⇓ value (int i₂) →
            i₁ ℤ+ i₂ ≡ i₃ →
            e₁ + e₂ ⇓ value (int i₃)

  e-minus : ∀ {e₁ e₂ i₁ i₂ i₃} →
            e₁ ⇓ value (int i₁) →
            e₂ ⇓ value (int i₂) →
            i₁ ℤ- i₂ ≡ i₃ →
            e₁ - e₂ ⇓ value (int i₃)

  e-times : ∀ {e₁ e₂ i₁ i₂ i₃} →
            e₁ ⇓ value (int i₁) →
            e₂ ⇓ value (int i₂) →
            i₁ ℤ* i₂ ≡ i₃ →
            e₁ * e₂ ⇓ value (int i₃)

  e-lt    : ∀ {e₁ e₂ i₁ i₂ b} →
            e₁ ⇓ value (int i₁) →
            e₂ ⇓ value (int i₂) →
            i₁ ℤ< i₂ ≡ b →
            e₁ < e₂ ⇓ value (bool b)

  -- Arise errors.
  e-PlusBoolL   : ∀ {e₁ e₂ b} → e₁ ⇓ value (bool b) → e₁ + e₂ ⇓ error
  e-PlusBoolR   : ∀ {e₁ e₂ b} → e₂ ⇓ value (bool b) → e₁ + e₂ ⇓ error
  e-PlusErrorL  : ∀ {e₁ e₂} → e₁ ⇓ error → e₁ + e₂ ⇓ error
  e-PlusErrorR  : ∀ {e₁ e₂} → e₂ ⇓ error → e₁ + e₂ ⇓ error

  e-MinusBoolL  : ∀ {e₁ e₂ b} → e₁ ⇓ value (bool b) → e₁ - e₂ ⇓ error
  e-MinusBoolR  : ∀ {e₁ e₂ b} → e₂ ⇓ value (bool b) → e₁ - e₂ ⇓ error
  e-MinusErrorL : ∀ {e₁ e₂} → e₁ ⇓ error → e₁ - e₂ ⇓ error
  e-MinusErrorR : ∀ {e₁ e₂} → e₂ ⇓ error → e₁ - e₂ ⇓ error
               
  e-TimesBoolL  : ∀ {e₁ e₂ b} → e₁ ⇓ value (bool b) → e₁ * e₂ ⇓ error
  e-TimesBoolR  : ∀ {e₁ e₂ b} → e₂ ⇓ value (bool b) → e₁ * e₂ ⇓ error
  e-TimesErrorL : ∀ {e₁ e₂} → e₁ ⇓ error → e₁ * e₂ ⇓ error
  e-TimesErrorR : ∀ {e₁ e₂} → e₂ ⇓ error → e₁ * e₂ ⇓ error

  e-LtBoolL     : ∀ {e₁ e₂ b} → e₁ ⇓ value (bool b) → e₁ < e₂ ⇓ error
  e-LtBoolR     : ∀ {e₁ e₂ b} → e₂ ⇓ value (bool b) → e₁ < e₂ ⇓ error
  e-LtErrorL    : ∀ {e₁ e₂} → e₁ ⇓ error → e₁ < e₂ ⇓ error
  e-LtErrorR    : ∀ {e₁ e₂} → e₂ ⇓ error → e₁ < e₂ ⇓ error

  e-IfInt    : ∀ {e₁ e₂ e₃ i} →
               e₁ ⇓ value (int i) →
               IF e₁ THEN e₂ ELSE e₃ ⇓ error
  e-IfError  : ∀ {e₁ e₂ e₃} →
               e₁ ⇓ error →
               IF e₁ THEN e₂ ELSE e₃ ⇓ error
  e-IfTError : ∀ {e₁ e₂ e₃} →
               e₁ ⇓ value (bool true) →
               e₂ ⇓ error →
               IF e₁ THEN e₂ ELSE e₃ ⇓ error
  e-IfFError : ∀ {e₁ e₂ e₃} →
               e₁ ⇓ value (bool false) →
               e₃ ⇓ error →
               IF e₁ THEN e₂ ELSE e₃ ⇓ error

-- Typing rules.
data _∶_ : Exp → Type → Set where
  t-Int   : ∀ {i} → VAL (int i) ∶ int
  t-Bool  : ∀ {b} → VAL (bool b) ∶ bool
  t-If    : ∀ {e₁ e₂ e₃ τ} →
            e₁ ∶ bool → e₂ ∶ τ → e₃ ∶ τ →
            IF e₁ THEN e₂ ELSE e₃ ∶ τ
  t-Plus  : ∀ {e₁ e₂} → e₁ ∶ int → e₂ ∶ int → e₁ + e₂ ∶ int
  t-Minus : ∀ {e₁ e₂} → e₁ ∶ int → e₂ ∶ int → e₁ - e₂ ∶ int
  t-Times : ∀ {e₁ e₂} → e₁ ∶ int → e₂ ∶ int → e₁ * e₂ ∶ int
  t-Lt    : ∀ {e₁ e₂} → e₁ ∶ int → e₂ ∶ int → e₁ < e₂ ∶ bool

-- Utilities.
ip : ℕ → Val -- integer plus value
ip n = int (+ n)
-_ : ℕ → ℤ
- n = -[1+ n ] ℤ+ (+ 1)
im : ℕ → Val -- integer minus value
im n = int (- n)

-- Exercises.
ex8-1-1 : VAL (ip 3) + VAL (ip 5) ∶ int
ex8-1-1 = t-Plus t-Int t-Int

-- Type safety for TypingML1.
thm8-1′ : ∀ {e τ r} →
         e ∶ τ →
         e ⇓ r →
         (∃ λ (v : Val) → (r ≡ value v) ×
                            ((τ ≡ int  → ∃ λ (i : ℤ) → v ≡ int i) ×
                             (τ ≡ bool → ∃ λ (b : Bool) → v ≡ bool b)))
-- -- Successfully evaluated.
thm8-1′ (t-Int {i}) e-int = int i , (refl , ((λ _ → i , refl) , λ ()))
thm8-1′ (t-Bool {b}) e-bool = bool b , (refl , ((λ ()) , (λ _ → b , refl)))

thm8-1′ (t-Plus _ _) (e-plus  {i₁ = i₁} {i₂ = i₂} {i₃ = .(i₁ ℤ+ i₂)} _ _ refl) =
  int (i₁ ℤ+ i₂) , (refl , (λ x → i₁ ℤ+ i₂ , refl) , (λ ()))
thm8-1′ (t-Minus _ _) (e-minus {i₁ = i₁} {i₂ = i₂} {i₃ = .(i₁ ℤ- i₂)} _ _ refl) =
  int (i₁ ℤ- i₂) , (refl , (λ x → i₁ ℤ- i₂ , refl) , (λ ()))
thm8-1′ (t-Times _ _) (e-times {i₁ = i₁} {i₂ = i₂} {i₃ = .(i₁ ℤ* i₂)} _ _ refl) =
  int (i₁ ℤ* i₂) , (refl , (λ x → i₁ ℤ* i₂ , refl) , (λ ()))
thm8-1′ (t-Lt _ _)    (e-lt    {i₁ = i₁} {i₂ = i₂} {b = .(i₁ ℤ< i₂)} _ _ refl) =
  bool (i₁ ℤ< i₂) , (refl , (λ ()) , (λ x → i₁ ℤ< i₂ , refl))

thm8-1′ (t-If p₁ p₂ p₃) (e-ift d₁ d₂) = thm8-1′ p₂ d₂
thm8-1′ (t-If p₁ p₂ p₃) (e-iff d₁ d₂) = thm8-1′ p₃ d₂

-- -- Evaluation failed.
thm8-1′ (t-Plus p _) (e-PlusBoolL d) with thm8-1′ p d
-- p states that e ∶ int.
-- d states that e ⇓ value (bool b).
-- thm8-1′ p d is
--   ∃ λ (v : Val) → (value (bool b) ≡ value v) ×
--                     ((int ≡ int  → ∃ λ (i : ℤ) → v ≡ int i) ×
--                      (int ≡ bool → ∃ λ (b : Bool) → v ≡ bool b))).
-- Case v of
--   int.  In this case (value (bool b) ≡ value v) should be empty.
... | int _ , () , _
--   bool.  Then f is (int ≡ int → ∃ λ (i : ℤ) → v ≡ int i).
... | bool _ , refl , f , _ with f refl -- f consumes only refl, and
...     | _ , ()                        -- f refl is ∃ λ (i : ℤ) → v ≡ int i,
                                        -- where v ≡ int i should be empty.

thm8-1′ (t-Plus _ p) (e-PlusBoolR d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
... | _ , ()

thm8-1′ (t-Plus p _) (e-PlusErrorL d) with thm8-1′ p d
-- p states that e ∶ int.
-- d states that e ⇓ error.
-- thm8-1′ p d is
--   ∃ λ (v : Val) → (error ≡ value v) × ...
--   where error ≡ value v should be empty
... | _ , () , _

thm8-1′ (t-Plus _ p) (e-PlusErrorR d) with thm8-1′ p d
... | _ , () , _

-- Minus.
thm8-1′ (t-Minus p _) (e-MinusBoolL d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
...     | _ , ()
thm8-1′ (t-Minus _ p) (e-MinusBoolR d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
... | _ , ()
thm8-1′ (t-Minus p _) (e-MinusErrorL d) with thm8-1′ p d
... | _ , () , _
thm8-1′ (t-Minus _ p) (e-MinusErrorR d) with thm8-1′ p d
... | _ , () , _

-- Times.
thm8-1′ (t-Times p _) (e-TimesBoolL d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
...     | _ , ()
thm8-1′ (t-Times _ p) (e-TimesBoolR d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
... | _ , ()
thm8-1′ (t-Times p _) (e-TimesErrorL d) with thm8-1′ p d
... | _ , () , _
thm8-1′ (t-Times _ p) (e-TimesErrorR d) with thm8-1′ p d
... | _ , () , _

-- Lt.
thm8-1′ (t-Lt p _) (e-LtBoolL d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
...     | _ , ()
thm8-1′ (t-Lt _ p) (e-LtBoolR d) with thm8-1′ p d
... | int _ , () , _
... | bool _ , refl , f , _ with f refl
... | _ , ()
thm8-1′ (t-Lt p _) (e-LtErrorL d) with thm8-1′ p d
... | _ , () , _
thm8-1′ (t-Lt _ p) (e-LtErrorR d) with thm8-1′ p d
... | _ , () , _

thm8-1′ (t-If p _ _) (e-IfInt d) with thm8-1′ p d
-- p states that e ∶ bool
-- d states that e ⇓ value (int i)
-- thm8-1′ p d is
--   ∃ λ (v : Val) → (value (int i) ≡ value v) ×
--                     ((bool ≡ int  → ∃ λ (i : ℤ) → v ≡ int i) ×
--                      (bool ≡ bool → ∃ λ (i : ℤ) → v ≡ bool i))).
-- Case v of
--   bool.
... | bool _ , () , _
--   int.  
... | int _ , refl , _ , g with g refl
...     | _ , ()

thm8-1′ (t-If p _ _) (e-IfError d) with thm8-1′ p d
... | _ , () , _

thm8-1′ (t-If _ p _) (e-IfTError _ d) with thm8-1′ p d
... | _ , () , _

thm8-1′ (t-If _ _ p) (e-IfFError _ d) with thm8-1′ p d
... | _ , () , _

