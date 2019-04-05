module TLP where

open import Data.Bool
open import Data.Nat
open import Data.String
open import Data.String.Base
open import Data.String.Properties renaming ( _==_ to primStringEquality )
open import Data.Empty
open import Data.Maybe
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl)


data Atom : Set where
  S : String → Atom
  N : ℕ → Atom

-- ----- Star型の定義 -----
data Star : Set where
  A : Atom → Star
  C   : Star → Star → Star

-- postulate
  -- Error : String
  -- nil : String
  -- tru : String
  -- err : String
  -- tru!=nil : ⊥

nil = "nil"

tru = "tru"

err = "err"

NIL : Star
NIL = A (S nil)

TRU : Star
TRU = A (S tru)

Error : Star
Error = A (S err)

-- 組み込み関数 
cons : (x y : Star) -> Star
cons x y = C x y


mcons : (x y : Maybe Star) → Star
mcons (just x) (just y) = (C x y)
mcons (just x) nothing = x
mcons nothing (just y) = y
mcons nothing nothing = NIL

car : (x : Star) -> Maybe Star
car (C x x₁) = just x
car x = just x

cdr : (x : Star) -> Maybe Star
cdr (C x x₁) = just x₁
cdr _ = nothing

atom : (x : Star) -> Bool
atom (C x x₁) = false
atom _ = true

eq : ℕ → ℕ → Bool
eq zero zero = true
eq (suc n) (suc m) = eq n m
eq _ _ = false


natp : (x : Star) → Star
natp (A (S x)) = NIL
natp (A (N x)) = TRU
natp (C x x₁) = NIL



{-# TERMINATING #-}
size : (x : Star) → ℕ
size (A x) = zero
size x with cdr x
size x | just x₁ = suc (size x₁)
size x | nothing = suc zero

-- ? (λ _ → suc) 0
-- List だと foldr つかって受け取ったら suc を返す関数 を定義
-- 最後に suc ~ zero にして全体が出る

-- star だと (C a b) を受け取って suc を返せば良い？

{--
size を出すには？
cons (C)の数 x 2 の数を出したい
C の数を数えるには…？
--}


sequal : (x y : Star) -> Star
sequal (A (S x)) (A (S y)) with primStringEquality x y
sequal (A (S x)) (A (S y)) | false = NIL
sequal (A (S x)) (A (S y)) | true = TRU
sequal (A (N x)) (A (N y)) with eq x y
sequal (A (N x)) (A (N y)) | false = NIL
sequal (A (N x)) (A (N y)) | true = TRU
sequal (C x x₁) (C y y₁) with sequal x y
sequal (C x x₁) (C y y₁) | A (S x₂) with primStringEquality x₂ tru
sequal (C x x₁) (C y y₁) | A (S x₂) | false = NIL
sequal (C x x₁) (C y y₁) | A (S x₂) | true with sequal x₁ y₁
sequal (C x x₁) (C y y₁) | A (S x₂) | true | A (S x₃) with primStringEquality x₃ tru
sequal (C x x₁) (C y y₁) | A (S x₂) | true | A (S x₃) | false = NIL
sequal (C x x₁) (C y y₁) | A (S x₂) | true | A (S x₃) | true = TRU
sequal (C x x₁) (C y y₁) | A (S x₂) | true | A (N x₃) = NIL
sequal (C x x₁) (C y y₁) | A (S x₂) | true | C a a₁ = NIL
sequal (C x x₁) (C y y₁) | A (N x₂) = NIL
sequal (C x x₁) (C y y₁) | C a a₁ = NIL
sequal _ _ = NIL

mequal : (x y : Maybe Star) -> Bool
mequal (just (A (N x))) (just (A (N x₁))) = eq x x₁
mequal (just (A (S x))) (just (A (S x₁))) = primStringEquality x x₁
mequal (just (C x x₂)) (just (C x₁ y)) = mequal (just x) (just x₁) ∧ mequal (just x₂) (just y)
mequal _ _ = false

cong : {a b : Set} {x y : a} (f : a → b) →  x ≡ y → f x ≡ f y
cong _ refl = refl

stringSame : (x : String) → primStringEquality x x ≡ true
stringSame x with (x Data.String.≟ x)
stringSame x | (Relation.Nullary.Dec.yes p) = refl
stringSame x | (Relation.Nullary.Dec.no ¬p) = ⊥-elim (¬p refl)

sequalSame : (x : Star) → sequal x x ≡ TRU
sequalSame (A (N zero)) = refl
sequalSame (A (N (suc x))) = sequalSame (A (N x))
sequalSame (A (S x)) with (x Data.String.≟ x)
sequalSame (A (S x)) | Relation.Nullary.yes p = refl
sequalSame (A (S x)) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
sequalSame (C x x₁) with sequal x x | sequalSame x
sequalSame (C x x₁) | A .(S "tru") | refl with sequal x₁ x₁ | sequalSame x₁
sequalSame (C x x₁) | A .(S _) | refl | A .(S "tru") | refl = refl


mequalSame : (x : Star) → mequal (just x) (just x) ≡ true
mequalSame (A (S x)) = stringSame x
mequalSame (A (N zero)) = refl
mequalSame (A (N (suc x))) = mequalSame (A (N x))
mequalSame (C x x₁) with mequal (just x) (just x) | mequalSame x
mequalSame (C x x₁) | true | refl with mequal (just x₁) (just x₁) | mequalSame x₁
mequalSame (C x x₁) | true | refl | true | refl = refl

-- cong ({!!}) (mequalSame x)

-- sequal _ _ = NIL

if : (x : Bool) (y z : Star) -> Star
if x y z with x
if x y z | false = z
if x y z | true = y


-- Cons の公理
atom/cons : (x y : Star) → ( (atom (cons x y)) ≡ false)
atom/cons x y = refl

car/cons : (x y : Star) → (mequal (car (cons x y)) (just x)) ≡ true
car/cons x y = mequalSame x

car/mcons : (x y : Star) → (mequal (car (mcons (just x) (just y))) (just x)) ≡ true
car/mcons x y = mequalSame x


cdr/cons : (x y : Star) → (mequal (cdr (cons x y)) (just y)) ≡ true
cdr/cons x y = mequalSame y

cdr/mcons : (x y : Star) → (mequal (cdr (mcons (just x) (just y))) (just y)) ≡ true
cdr/mcons x y = mequalSame y

b2s : (x : Bool) → Star
b2s false = NIL
b2s true = TRU

m2s : (x : Maybe Star) → Star
m2s (just x) = x
m2s nothing = NIL

-- IF の公理
if-same : (x : Bool) (y : Star) → mequal (just (if x y y)) (just y) ≡ true
if-same x y with primStringEquality tru nil
if-same false y | false = mequalSame y
if-same true y | false = mequalSame y
if-same false y | true = mequalSame y
if-same true y | true = mequalSame y

if-true : (x : Bool ) ( y : Star) → (mequal (just (if true TRU y)) (just TRU)) ≡ true
if-true x y with primStringEquality tru nil
if-true x y | false = refl
if-true x y | true = refl

if-false : (x : Bool) (y : Star) → (mequal (just (if false TRU y)) (just y)) ≡ true
if-false x y with primStringEquality tru nil
if-false x y | false = mequalSame y
if-false x y | true = mequalSame y

if-nest-A : (x : Bool) (y z : Star) → (if x (sequal (if x y z) y) TRU) ≡ TRU
if-nest-A x y z with primStringEquality tru nil
if-nest-A false y z | false = refl
if-nest-A true y z | false = sequalSame y
if-nest-A false y z | true = refl
if-nest-A true y z | true = sequalSame y

if-nest-E : (x : Bool) (y z : Star) → (if x TRU (sequal (if x y z) z)) ≡ TRU
if-nest-E x y z with primStringEquality tru nil
if-nest-E false y z | false = sequalSame z
if-nest-E true y z | false = refl
if-nest-E false y z | true = sequalSame z
if-nest-E true y z | true = refl

cons/car+cdr : (x : Star) → (if false TRU (sequal (mcons (car x) (cdr x)) x)) ≡ TRU
cons/car+cdr x with primStringEquality nil tru
cons/car+cdr (A (S x)) | false = sequalSame (A (S x))
cons/car+cdr (A (N x)) | false = sequalSame (A (N x))
cons/car+cdr (C x x₁) | false with sequal x x | sequalSame x
cons/car+cdr (C x x₁) | false | A .(S "tru") | refl with sequal x₁ x₁ | sequalSame x₁
cons/car+cdr (C x x₁) | false | A .(S _) | refl | A .(S "tru") | refl = refl
cons/car+cdr (A (S x)) | true = sequalSame (A (S x))
cons/car+cdr (A (N x)) | true = sequalSame (A (N x))
cons/car+cdr (C x x₁) | true with sequal x x | sequalSame x
cons/car+cdr (C x x₁) | true | A .(S "tru") | refl with sequal x₁ x₁ | sequalSame x₁
cons/car+cdr (C x x₁) | true | A .(S _) | refl | A .(S "tru") | refl = refl




natp/size : (x : Star) → (mequal (just (natp (A (N (size x))))) (just TRU)) ≡ true
natp/size x = refl

