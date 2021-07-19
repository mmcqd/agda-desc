{-# OPTIONS --type-in-type #-}

open import Data.Unit renaming (tt to [])
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Fin
import Data.Nat

variable
  A B C : Set


infixr 7 _`×_
data Desc : Set where
  `1 : Desc
  `ind : Desc
  _`×_ : Desc → Desc → Desc
  `Σ `Π : (A : Set) (B : A → Desc) → Desc

infix 100 `_
`_ : Set → Desc
` A = `Σ A λ _ → `1

`∃ : (A → Desc) → Desc
`∃ B = `Σ _ B

⟦_⟧ : Desc → Set → Set
⟦ `1 ⟧ _ = ⊤
⟦ `ind ⟧ X = X
⟦ D `× D₁ ⟧ X = ⟦ D ⟧ X × ⟦ D₁ ⟧ X
⟦ `Σ A B ⟧ X = Σ A λ a → ⟦ B a ⟧ X
⟦ `Π A B ⟧ X = (a : A) → ⟦ B a ⟧ X

data μ (D : Desc) : Set where
  con : ⟦ D ⟧ (μ D) → μ D




IH : {D : Desc} → (A → Set) → ⟦ D ⟧ A → Set
IH {D = `1} P xs = ⊤
IH {D = `ind} P xs = P xs
IH {D = D `× D₁} P (xs , ys) = IH P xs × IH P ys
IH {D = `Σ A B} P (a , xs) = IH P xs
IH {D = `Π A B} P f = (a : A) → IH P (f a) 

D-Alg : {D : Desc} → (μ D → Set) → Set
D-Alg {D} P = (xs : ⟦ D ⟧ (μ D)) → IH P xs → P (con xs)


-- The definition of ind given in the Levitation paper fails the termination
-- checker (though it is in fact terminating). This definition from 
-- Pierre-Evariste Dagand's thesis pases tho
ind : {D : Desc} {P : μ D → Set} → D-Alg P → (x : μ D) → P x
ind {D} {P} d-alg = induct
  where
    induct : (x : μ D) → P x
    ih : (D' : Desc) (xs : ⟦ D' ⟧ (μ D)) → IH P xs

    induct (con xs) = d-alg xs (ih D xs)
    ih `1 xs = []
    ih `ind xs = induct xs
    ih (D' `× D'') (xs , ys) = ih D' xs , ih D'' ys
    ih (`Σ A B) (a , xs) = ih (B a) xs
    ih (`Π A B) f = λ a → ih (B a) (f a)


fmap : (D : Desc) → (A → B) → ⟦ D ⟧ A → ⟦ D ⟧ B
fmap `1 f [] = []
fmap `ind f xs = f xs
fmap (D `× D₁) f (fst , snd) = fmap D f fst , fmap D₁ f snd
fmap (`Σ A B) f (fst , snd) = fst , fmap (B fst) f snd
fmap (`Π A B) f xs = λ a → fmap (B a) f (xs a)


π : ∀ {n} → (Fin n → Set) → Set
π {Data.Nat.zero} P = ⊤
π {Data.Nat.suc n} P = P zero × π λ x → P (suc x)

switch : ∀ {n} {P : Fin n → Set} → π P → (x : Fin n) → P x
switch f zero = proj₁ f
switch f (suc x) = switch (proj₂ f) x




-- Some fun syntax for writing described types

infixr 5 _∣_
_∣_ : A → B → A × B
_∣_ = _,_

infix 6 _∙ 
_∙ : A → A × ⊤
A ∙ = A , []

infix 1 `desc_
`desc_ : ∀ {n} → π {n} (λ _ → Desc) → Desc
`desc_ = `∃ ∘ switch

infix 1 `data_
`data_ : ∀ {n} → π {n} (λ _ → Desc) → Set
`data_ = μ ∘ `desc_


Bool : Set
Bool = `data
    `1 
  ∣ `1 
  ∙

true : Bool
true = con (zero , [])

false : Bool
false = con (suc zero , []) 


Nat : Set
Nat = `data
    `1 
  ∣ `ind
  ∙

Z : Nat
Z = con (zero , [])

S : Nat → Nat
S x = con (suc zero , x)

Vec : Set → Nat → Set
Vec A = ind λ{ (zero , snd) ih → ⊤
             ; (suc zero , snd) ih → A × ih}

vnil : ∀ {A} → Vec A Z
vnil = []

vcons : ∀ {A n} → A → Vec A n → Vec A (S n)
vcons = _,_



Zero : Set
Zero = `data []


_⊎_ : Set → Set → Set
A ⊎ B = `data
    ` A 
  ∣ ` B
  ∙ 


inl : A → A ⊎ B
inl x = con (zero , x , [])

inr : B → A ⊎ B
inr x = con (suc zero , x , [])


record Iso (A B : Set) : Set where
  constructor iso
  field
    f : A → B
    g : B → A
    gf : (x : A) → g (f x) ≡ x
    fg : (x : B) → f (g x) ≡ x
  
iso/Bool/⊤⊎⊤ : Iso Bool (⊤ ⊎ ⊤)
iso/Bool/⊤⊎⊤ = iso f g gf fg
  where
    f = ind λ{(zero , []) _ → inl []
            ; (suc zero , []) _ → inr []}
    
    g = ind λ{(zero , [] , []) _ → true
            ; (suc zero , [] , []) _ → false}

    gf = ind λ{(zero , []) _ → refl
             ; (suc zero , []) _ → refl}
    
    fg = ind λ{(zero , [] , []) _ → refl
             ; (suc zero , [] , []) _ → refl}


List : Set → Set
List A = `data
    `1
  ∣ ` A `× `ind
  ∙

nil : ∀ {A} → List A
nil = con (zero , [])

cons : ∀ {A} → A → List A → List A
cons x xs = con (suc zero , (x , []) , xs)

Tree : Set → Set
Tree A = `data
    `1
  ∣ ` A `× `ind `× ` A
  ∙

empty : ∀ {A} → Tree A
empty = con (zero , [])

node : ∀ {A} → Tree A → A → Tree A → Tree A
node l x r = con (suc zero , (x , []) , (r , (x , [])))

Maybe : Set → Set
Maybe A = `data
    `1
  ∣ ` A
  ∙

none : ∀ {A} → Maybe A
none = con (zero , [])

some : ∀ {A} → A → Maybe A
some x = con (suc zero , x , [])


-- Desc implemented as a Desc, no levitation tho, since `Desc is not implemented using `Desc

`Desc : Set
`Desc = `data
    `1                             -- `1
  ∣ `1                             -- `ind
  ∣ `ind `× `ind                   -- `×
  ∣ `Σ Set (λ A → `Π A λ _ → `ind) -- `Σ
  ∣ `Σ Set (λ A → `Π A λ _ → `ind) -- `Π
  ∙

`1` : `Desc
`1` = con (zero , [])

`ind` : `Desc
`ind` = con (suc zero , [])

_`×`_ : `Desc → `Desc → `Desc
D `×` D₁ = con (suc (suc zero) , D₁ , D₁)

`Σ` : (A : Set) → (A → `Desc) → `Desc
`Σ` A B = con (suc (suc (suc zero)) , A , B)

`Π` : (A : Set) → (A → `Desc) → `Desc
`Π` A B = con (suc (suc (suc (suc zero))) , A , B)


`⟦_⟧` : `Desc → Set → Set
`⟦ D ⟧` X = ind d-alg D
  where
    d-alg : _
    d-alg (zero , args) ih = ⊤
    d-alg (suc zero , args) ih = X
    d-alg (suc (suc zero) , args) (fst , snd) = fst × snd
    d-alg (suc (suc (suc zero)) , fst , snd) ih = Σ fst ih
    d-alg (suc (suc (suc (suc zero))) , fst , snd) ih = (x : fst) → ih x


