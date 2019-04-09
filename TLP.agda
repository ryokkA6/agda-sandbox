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
  C : Atom → Star → Star

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
cons (A x) y = C x y
cons (C x x₁) y = C x (cons x₁ y)


mcons : (x y : Maybe Star) → Star
mcons (just x) (just y) = (cons x y)
mcons (just x) nothing = x
mcons nothing (just y) = y
mcons nothing nothing = NIL

car : (x : Star) -> Star
car (C x x₁) = A x
car x = x

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


natp : (x : Star) → Bool
natp (A (S x)) = false
natp (A (N x)) = true
natp (C x x₁) = false

< : (x y : ℕ ) → Bool
< n zero = false
< zero (suc m) = true
< (suc n) (suc m) = (< n m)

natlt : (x : ℕ) → < x (suc x) ≡ true
natlt zero = refl
natlt (suc x) = natlt x

size : (x : Star) → ℕ
size (A x) = zero
size (C x x₁) = suc (size x₁)

-- size-test
createcons : ℕ → Star
createcons (suc x) = (cons (A (N x)) (createcons x))
createcons zero = NIL

sizet = λ x → size (createcons x)

-- <-test
-- C-C, C-n, "<t 20 10".  Agda return true
<t = λ x y → (< x y)

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
sequal (A (S x)) (A (S x₁)) with x == x₁
sequal (A (S x)) (A (S x₁)) | false = NIL
sequal (A (S x)) (A (S x₁)) | true = TRU
sequal (A (N x)) (A (N x₁)) with  x Data.Nat.≟ x₁
sequal (A (N x)) (A (N x₁)) | Relation.Nullary.yes p = TRU
sequal (A (N x)) (A (N x₁)) | Relation.Nullary.no ¬p = NIL
sequal (C (S x) x₁) (C (S x₂) y) with x == x₂
sequal (C (S x) x₁) (C (S x₂) y) | false = NIL
sequal (C (S x) x₁) (C (S x₂) y) | true = sequal x₁ y
sequal (C (N x) x₁) (C (N x₂) y) with  x Data.Nat.≟ x₂
sequal (C (N x) x₁) (C (N x₂) y) | Relation.Nullary.yes p = sequal x₁ y
sequal (C (N x) x₁) (C (N x₂) y) | Relation.Nullary.no ¬p = NIL
sequal _ _ = NIL

mequal : (x y : Maybe Star) -> Bool
mequal (just (A (N x))) (just (A (N x₁))) with x Data.Nat.≟ x₁
... | a = true
mequal (just (A (S x))) (just (A (S x₁))) = primStringEquality x x₁
mequal (just (C (S x) x₂)) (just (C (S x₁) y)) with x == x₁
mequal (just (C (S x) x₂)) (just (C (S x₁) y)) | false = false
mequal (just (C (S x) x₂)) (just (C (S x₁) y)) | true = mequal (just x₂) (just y)
mequal (just (C (N x) x₂)) (just (C (N x₁) y)) with x Data.Nat.≟ x₁
mequal (just (C (N x) x₂)) (just (C (N x₁) y)) | Relation.Nullary.yes p = mequal (just x₂) (just y)
mequal (just (C (N x) x₂)) (just (C (N x₁) y)) | Relation.Nullary.no ¬p = false
mequal _ _ = false

cong : {a b : Set} {x y : a} (f : a → b) →  x ≡ y → f x ≡ f y
cong _ refl = refl

stringSame : (x : String) → primStringEquality x x ≡ true
stringSame x with (x Data.String.≟ x)
stringSame x | (Relation.Nullary.Dec.yes p) = refl
stringSame x | (Relation.Nullary.Dec.no ¬p) = ⊥-elim (¬p refl)

sequalSame : (x : Star) → sequal x x ≡ TRU
sequalSame (A (S x)) with (x Data.String.≟ x)
sequalSame (A (S x)) | Relation.Nullary.yes p = refl
sequalSame (A (S x)) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
sequalSame (A (N x)) with x Data.Nat.≟ x
sequalSame (A (N x)) | Relation.Nullary.yes p = refl
sequalSame (A (N x)) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
sequalSame (C (S x) x₁) with x Data.String.≟ x
sequalSame (C (S x) x₁) | Relation.Nullary.yes p = sequalSame x₁
sequalSame (C (S x) x₁) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
sequalSame (C (N x) x₁) with x Data.Nat.≟ x
sequalSame (C (N x) x₁) | Relation.Nullary.yes p = sequalSame x₁
sequalSame (C (N x) x₁) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)

mequalSame : (x : Star) → mequal (just x) (just x) ≡ true
mequalSame (A (S x)) with (x Data.String.≟ x)
mequalSame (A (S x)) | Relation.Nullary.yes p = refl
mequalSame (A (S x)) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
mequalSame (A (N x)) with x Data.Nat.≟ x
... | a = refl
mequalSame (C (S x) x₁) with (x Data.String.≟ x)
mequalSame (C (S x) x₁) | Relation.Nullary.yes p = mequalSame x₁
mequalSame (C (S x) x₁) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)
mequalSame (C (N x) x₁) with x Data.Nat.≟ x
mequalSame (C (N x) x₁) | Relation.Nullary.yes p = mequalSame x₁
mequalSame (C (N x) x₁) | Relation.Nullary.no ¬p = ⊥-elim (¬p refl)


if : (x : Bool) (y z : Star) -> Star
if x y z with x
if x y z | false = z
if x y z | true = y

-- -- Cons の公理
atom/cons : (x y : Star) → ((atom (cons x y)) ≡ false)
atom/cons (A x) y = refl
atom/cons (C x x₁) y = refl

car/cons : (x : Atom) (y : Star) → (mequal (just (car (cons (A x) y))) (just (A x))) ≡ true
car/cons (S x) y = mequalSame (A (S x))
car/cons (N x) y = refl

-- car/mcons : (x y : Star) → (mequal (just (car (mcons (just x) (just y)))) (just x)) ≡ true
-- car/mcons x y = {!!}


cdr/cons : (x : Atom) (y : Star) → (mequal (cdr (cons (A x) y)) (just y)) ≡ true
cdr/cons x (A x₁) = mequalSame (A x₁)
cdr/cons x (C x₁ y) = mequalSame (C x₁ y)

-- cdr/mcons : (x y : Star) → (mequal (cdr (mcons (just x) (just y))) (just y)) ≡ true
-- cdr/mcons x y = {!!}

b2s : (x : Bool) → Star
b2s false = NIL
b2s true = TRU

s2b : (x : Star) → Bool
s2b (A (S x)) with x == nil
s2b (A (S x)) | false = true
s2b (A (S x)) | true = false
s2b (A (N zero)) = false
s2b (A (N (suc x))) = true
s2b (C x x₁) = false

m2s : (x : Maybe Star) → Star
m2s (just x) = x
m2s nothing = NIL

-- -- IF の公理
if-same : (x : Bool) (y : Star) → mequal (just (if x y y)) (just y) ≡ true
if-same x y with primStringEquality tru nil
if-same false y | false = mequalSame y
if-same true y | false = mequalSame y
if-same false y | true = mequalSame y
if-same true y | true = mequalSame y

if-same2 : (x : Bool) (y : Star) → (if x y y) ≡ y
if-same2 false y = refl
if-same2 true y = refl

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


-- (atom x) をどうするかわかんなかったからとりあえず false をおいてる
cons/car+cdr : (x : Star) → (if (atom x) TRU (sequal (mcons (just (car x)) (cdr x)) x)) ≡ TRU
cons/car+cdr x with atom x
cons/car+cdr (A x) | false = sequalSame (A x)
cons/car+cdr (C x x₁) | false = sequalSame (C x x₁)
cons/car+cdr x | true = refl

natp/size : (x : Star) → (mequal (just (b2s (natp (A (N (size x)))))) (just TRU)) ≡ true
natp/size x = refl

size/car : (x : Star) → (if (atom x) TRU (sequal (b2s (< (size (car x)) (size x))) TRU)) ≡ TRU
size/car (A x) = refl
size/car (C x x₁) with (atom (C x x₁))
size/car (C x x₁) | true = refl
size/car (C x x₁) | false = refl


size/cdr : (x : Star)  → (if (atom x) TRU (b2s (< (size (m2s (cdr x))) (size x)))) ≡ TRU
size/cdr (A x) = refl
size/cdr (C x x₁) rewrite natlt (size x₁) = refl


memb? : (xs : Star) → Bool
memb? (A x) = false
memb? (C (N x) xs) = false
memb? (C (S x) xs) with x Data.String.≟ "?"
memb? (C (S x) xs) | Relation.Nullary.yes p = true
memb? (C (S x) xs) | Relation.Nullary.no ¬p = false

membproof : (xs : Star) → (if (natp (A (N (size xs))))
                              (if (atom xs)
                                TRU
                                (if (mequal (just (car xs)) (just (A (S "?"))))
                                      TRU
                                      (b2s (< (size (m2s (cdr xs))) (size xs)))))
                                      NIL) ≡ TRU

membproof (A x) = refl
membproof (C x xs) rewrite natlt (size xs) | if-same2 (mequal (just (A x)) (just (A (S "?")))) TRU = refl

remb : (xs : Star) → Star
remb (A (S x)) with x Data.String.≟ "?"
remb (A (S x)) | Relation.Nullary.yes p = NIL
remb (A (S x)) | Relation.Nullary.no ¬p = (A (S x))
remb (A (N x)) = (A (N x))
remb (C (S x) x₁) with x Data.String.≟ "?"
remb (C (S x) x₁) | Relation.Nullary.yes p = (remb x₁)
remb (C (S x) x₁) | Relation.Nullary.no ¬p = cons (A (S x)) (remb x₁)
remb (C (N x) x₁) = cons (A (N x)) (remb x₁)


rembproof : (xs : Star) → (if (natp (A (N (size xs))))
                              (if (atom xs)
                                TRU
                                (if (mequal (just (car xs)) (just (A (S "?"))))
                                  (b2s (< (size (m2s (cdr xs))) (size xs)))
                                  (b2s (< (size (m2s (cdr xs))) (size xs)))))
                              NIL ) ≡ TRU
rembproof (A x) = refl
rembproof (C x xs) rewrite membproof (C x xs) | natlt (size xs) | if-same2 (mequal (just (A x)) (just (A (S "?")))) TRU = refl


memb?/remb : (xs : Star) → (memb? (remb xs)) ≡ false
memb?/remb (A (S x)) with x Data.String.≟ "?"
memb?/remb (A (S x)) | Relation.Nullary.yes p = refl
memb?/remb (A (S x)) | Relation.Nullary.no ¬p = refl
memb?/remb (A (N x)) = refl
memb?/remb (C (S x) xs) with x Data.String.≟ "?"
memb?/remb (C (S x) xs) | Relation.Nullary.yes p = memb?/remb xs
memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p with x Data.String.≟ "?"
memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p | Relation.Nullary.yes p = ⊥-elim (¬p p)
memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p | Relation.Nullary.no ¬p₁ = refl
memb?/remb (C (N x) xs) = refl

-- memb?/remb (A (S x)) with x Data.String.≟ "?"
-- memb?/remb (A (S x)) | Relation.Nullary.yes p = refl
-- memb?/remb (A (S x)) | Relation.Nullary.no ¬p = refl
-- memb?/remb (A (N x)) = refl
-- memb?/remb (C (S x) xs) with x Data.String.≟ "?"

-- memb?/remb (C (S x) xs) | Relation.Nullary.yes p = memb?/remb xs
-- memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p with x Data.String.≟ "?"
-- memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p | Relation.Nullary.yes p = ⊥-elim (¬p p)
-- memb?/remb (C (S x) xs) | Relation.Nullary.no ¬p | Relation.Nullary.no ¬p₁ = refl
-- memb?/remb (C (N x) xs) = refl
