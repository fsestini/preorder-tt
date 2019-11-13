{-# OPTIONS --prop --without-K #-}

module Main where

open import Agda.Primitive

variable l i j k : Level

record ΣP (P : Prop i) (Q : P -> Prop j) : Prop (i ⊔ j) where
  constructor _,P_
  field
    fst : P
    snd : Q fst
open ΣP

_×_ : Prop i -> Prop j -> Prop (i ⊔ j)
A × B = ΣP A λ _ → B

record Preorder (l : Level) : Set (lsuc l) where
  field
    ∣_∣ : Set l
    _<_ : ∣_∣ -> ∣_∣ -> Prop l
    R   : ∀ x -> x < x
    T   : ∀ {x y z} -> x < y -> y < z -> x < z
open Preorder

Con = Preorder

record _⟶_ (P : Preorder l) (Q : Preorder j) : Set (l ⊔ j) where
  private
    _<P_ = _<_ P
    _<Q_ = _<_ Q
  field
    fn : ∣ P ∣ -> ∣ Q ∣
    fn-rel : ∀{x y} -> x <P y -> fn x <Q fn y
open _⟶_

record Ty (j : Level) {i} (Γ : Preorder i) : Set (i ⊔ lsuc j) where
--  no-eta-equality
  private
    _<Γ_ = _<_ Γ
  field
    ∣_∣* : ∣ Γ ∣ -> Preorder j
    subst* : ∀{x y} -> x <Γ y -> ∣ x ∣* ⟶ ∣ y ∣*
    refl*₁ : ∀{γ x} -> let _<<_ = _<_ ∣ γ ∣*
                      in fn (subst* (R Γ γ)) x << x
    refl*₂ : ∀{γ x} -> let _<<_ = _<_ ∣ γ ∣*
                      in x << fn (subst* (R Γ γ)) x
    trans*₁ : ∀ {x y z k} {p : x <Γ y} {q : y <Γ z}
           -> let _<<_ = _<_ ∣ _ ∣*
              in fn (subst* (T Γ p q)) k << fn (subst* q) (fn (subst* p) k)
    trans*₂ : ∀ {x y z k} {p : x <Γ y} {q : y <Γ z}
           -> let _<<_ = _<_ ∣ _ ∣*
              in fn (subst* q) (fn (subst* p) k) << fn (subst* (T Γ p q)) k
open Ty

record ⊤ : Set i where
  constructor tt
record ⊤P : Prop i where
  constructor ttP

● : Con lzero
● = record
  { ∣_∣ = ⊤
  ; _<_ = λ _ _ → ⊤P
  ; R = λ _ → ttP
  ; T = λ _ _ → ttP
  }

open import Data.Product

_︐_ : (Γ : Con i) -> Ty j Γ -> Con (i ⊔ j)
Γ ︐ A = record
  { ∣_∣ = Σ ∣ Γ ∣ λ γ → ∣ ∣ A ∣* γ ∣
  ; _<_ = λ { (γ , a) (γ' , a') → ΣP (γ <Γ γ') λ p →
     let _<<_ = _<_ (∣ A ∣* γ') in fn (subst* A p) a << a' }
  ; R = λ { (γ , x) → R Γ γ ,P refl*₁ A }
  ; T = λ { {γ , a} {γ' , a'} {γ'' , a''}
            (p ,P q) (p' ,P q') →
         let
           Aγ'' = ∣ A ∣* γ''
           _<<_ = _<_ (∣ A ∣* γ'')
         in T Γ p p' ,P T Aγ'' (trans*₁ A {p = p} {q = p'})
            (T Aγ'' (fn-rel (subst* A p') q) q') }
  }
  where _<Γ_ = _<_ Γ

_ᵒᵖ : Con i -> Con i
Γ ᵒᵖ = record
  { ∣_∣ = ∣ Γ ∣ ; _<_ = λ x y → y <Γ x ; R = λ _ → R Γ _ ; T = λ x y → T Γ y x }
  where _<Γ_ = _<_ Γ

_︐ᵒᵖ_ : (Γ : Con i) -> Ty j (Γ ᵒᵖ) -> Con (i ⊔ j)
Γ ︐ᵒᵖ A = record
  { ∣_∣ = Σ ∣ Γ ∣ λ γ → ∣ ∣ A ∣* γ ∣
  ; _<_ = λ { (γ , a) (γ' , a') → ΣP (γ <Γ γ') λ p →
      let _<<_ = _<_ (∣ A ∣* γ) in a << fn (subst* A p) a'  }
  ; R = λ { (γ , x) → R Γ γ ,P refl*₂ A }
  ; T = λ { {γ , a} {γ' , a'} {γ'' , a''}
            (p ,P q) (p' ,P q') →
            let Aγ = ∣ A ∣* γ
            in T Γ p p' ,P T Aγ q (T Aγ (fn-rel (subst* A p) q') (trans*₂ A)) }
  }
  where _<Γ_ = _<_ Γ

record Tm (Γ : Con i) (A : Ty j Γ) : Set (i ⊔ j) where
  private
    _<Γ_ = _<_ Γ
  field
    tm : ∀ γ -> ∣ ∣ A ∣* γ ∣
    tm-rel : ∀{γ γ'} ->
             let _<<_ = _<_ (∣ A ∣* γ')
             in (p : γ <Γ γ') -> fn (subst* A p) (tm γ) << tm γ'
open Tm

variable Γ Δ Θ ∇ : Con i

record Lift (P : Prop i) : Prop (lsuc i) where
  constructor lift
  field
    unlift : P
open Lift

record LiftProp (P : Prop i) : Set i where
  constructor liftProp
  field
    unliftProp : P
open LiftProp


Prop-ty : Ty (lsuc j) Γ
Prop-ty {j} = record
  { ∣_∣* = λ γ → record
    { ∣_∣ = Prop j
    ; _<_ = λ P Q → Lift (P -> Q)
    ; R = λ x → lift (λ z → z)
    ; T = λ f g -> lift (λ x → unlift g (unlift f x))
    }
  ; subst* = λ p → record
    { fn = λ x → x
    ; fn-rel = λ x → x
    }
  ; refl*₁ = lift (λ x₁ → x₁)
  ; refl*₂ = lift (λ x₁ → x₁)
  ; trans*₁ = lift (λ x₁ → x₁)
  ; trans*₂ = lift (λ x₁ → x₁)
  }

El : Tm Γ (Prop-ty {j}) -> Ty j Γ
El t = record
         { ∣_∣* = λ γ → record
           { ∣_∣ = LiftProp (tm t γ)
           ; _<_ = λ x y → ⊤P
           ; R = λ x → ttP
           ; T = λ {x} {y} {z} _ _ → ttP
           }
         ; subst* = λ p → record
           { fn = λ x → liftProp (unlift (tm-rel t p) (unliftProp x))
           ; fn-rel = λ _ → ttP
           }
         ; refl*₁ = {!!}
         ; refl*₂ = {!!}
         ; trans*₁ = {!!}
         ; trans*₂ = {!!}
         }

ty-op : Ty j Γ -> Ty j Γ
ty-op A = record
  { ∣_∣* = λ γ → (∣ A ∣* γ) ᵒᵖ
  ; subst* = λ p → record
    { fn = fn (subst* A p)
    ; fn-rel = fn-rel (subst* A p)
    }
  ; refl*₁ = {!!}
  ; refl*₂ = {!!}
  ; trans*₁ = {!!}
  ; trans*₂ = {!!}
  }

module _ (Γ : Preorder i) where

  Setoid : Preorder i
  Setoid = record
    { ∣_∣ = ∣ Γ ∣
    ; _<_ = λ γ γ' → ΣP (γ <Γ γ') λ _ → γ' <Γ γ
    ; R = λ x → R Γ x ,P R Γ x
    ; T = λ { (p ,P q) (p' ,P q') → T Γ p p' ,P T Γ q' q }
    }
    where _<Γ_ = _<_ Γ

module _ (A : Ty j Γ) where
  SetoidTy : Ty j Γ
  SetoidTy = record
    { ∣_∣* = λ γ → Setoid (∣ A ∣* γ)
    ; subst* = λ {γ γ'} p → record
      { fn = fn (subst* A p)
      ; fn-rel = λ { (q ,P q') →
          fn-rel (subst* A p) q ,P fn-rel (subst* A p) q' }
      }
    ; refl*₁ = refl*₁ A ,P refl*₂ A
    ; refl*₂ = refl*₂ A ,P refl*₁ A
    ; trans*₁ = trans*₁ A ,P trans*₂ A
    ; trans*₂ = trans*₂ A ,P trans*₁ A
    }

module _ (A : Ty j Γ) where

  un-setoid : Tm Γ (SetoidTy A) -> Tm Γ A
  un-setoid t = record { tm = tm t ; tm-rel = λ p → fst (tm-rel t p) }

  un-setoid-op : Tm Γ (SetoidTy A) -> Tm Γ (ty-op A)
  un-setoid-op t = record { tm = tm t ; tm-rel = λ p → snd (tm-rel t p) }

module _ {A : Ty j Γ} (a : Tm Γ (ty-op A)) (b : Tm Γ A) where

  _≺_ : Tm Γ (Prop-ty {j = j} {Γ = Γ})
  _≺_ = record
    { tm = λ γ → _<_ (∣ A ∣* γ) (tm a γ) (tm b γ)
    ; tm-rel = λ {γ γ'} p →
       let AA = ∣ A ∣* γ'
       in lift (λ q →
         T AA (T AA (tm-rel a p) (fn-rel (subst* A p) q)) (tm-rel b p))
    }

-- module _ {Δ : Con j} (Γ : Con i) where

--   rel : Δ ⟶ (Γ ᵒᵖ) -> Δ ⟶ Γ -> Tm Δ Prop-ty
--   rel γ₀ γ₁ = record
--     { tm = λ δ → _<_ Γ (fn γ₀ δ) (fn γ₁ δ)
--     ; tm-rel = λ p → lift λ q → T Γ (T Γ (fn-rel γ₀ p) q) (fn-rel γ₁ p)
--     }

module _ {A : Ty j Γ} (a : Tm Γ (SetoidTy A)) where

  Refl : Tm Γ (El (_≺_ {A = A} (un-setoid-op A a) (un-setoid A a)))
  Refl = record
    { tm = λ γ → liftProp (R (∣ A ∣* γ) _)
    ; tm-rel = λ _ → ttP
    }

ε : ∀ (Γ : Con i) -> Γ ⟶ ●
ε Γ = record
  { fn = λ _ → tt
  ; fn-rel = λ _ → ttP
  }

_[_] : Ty j Γ -> Δ ⟶ Γ -> Ty j Δ
A [ σ ] = record
  { ∣_∣* = λ δ → ∣ A ∣* (fn σ δ)
  ; subst* = λ p → subst* A (fn-rel σ p)
  ; refl*₁ = refl*₁ A
  ; refl*₂ = refl*₂ A
  ; trans*₁ = trans*₁ A
  ; trans*₂ = trans*₂ A
  }

_[_]' : {A : Ty j Γ} -> Tm Γ A -> (σ : Δ ⟶ Γ) -> Tm Δ (A [ σ ])
t [ σ ]' = record
  { tm = λ γ → tm t (fn σ γ)
  ; tm-rel = λ {δ} {δ'} p → tm-rel t (fn-rel σ p)
  }

ext : ∀{Γ : Con k} {Δ : Con i} {A : Ty j Δ}
    -> (σ : Γ ⟶ Δ) -> Tm Γ (A [ σ ]) -> Γ ⟶ (Δ ︐ A)
ext σ t = record
  { fn = λ γ → fn σ γ , tm t γ
  ; fn-rel = λ {γ γ'} p → fn-rel σ p ,P tm-rel t p
  }

Sigma : (A : Ty j Γ) -> Ty k (Γ ︐ A) -> Ty (j ⊔ k) Γ
Sigma {Γ = Γ} A B = record
  { ∣_∣* = λ γ → record
    { ∣_∣ = Σ ∣ ∣ A ∣* γ ∣ λ a → ∣ ∣ B ∣* (γ , a) ∣
    ; _<_ = λ { (a , b) (a' , b') →
       let _<A_ = _<_ (∣ A ∣* γ)
           _<B_ = _<_ (∣ B ∣* (γ , a'))
           Aγ = ∣ A ∣* γ
       in ΣP (a <A a') λ q → fn (subst* B (R Γ _ ,P T Aγ (refl*₁ A) q)) b <B b' }
    ; R = λ { (a , b) → R (∣ A ∣* γ) _ ,P refl*₁ B }
    ; T = λ { {a , b} {a' , b'} {a'' , b''} (p ,P q) (p' ,P q')
      → let B'' = ∣ B ∣* (γ , a'')
        in T (∣ A ∣* γ) p p' ,P
          T B'' (T B'' (trans*₁ B)
            (fn-rel (subst* B (R Γ _ ,P T (∣ A ∣* γ) (refl*₁ A) p')) q)) q' }
    }
  ; subst* = λ {γ γ'} p → record
    { fn = λ { (a , b) → fn (subst* A p) a , fn (subst* B (p ,P R (∣ A ∣* γ') _)) b }
    ; fn-rel = λ { {a , b} {a' , b'} (q ,P q')
      -> let BB = ∣ B ∣* (γ' , fn (subst* A p) a')
         in fn-rel (subst* A p) q ,P T BB (T BB (trans*₂ B) (trans*₁ B))
           (fn-rel (subst* B (p ,P R (∣ A ∣* γ') _)) q') }
    }
  ; refl*₁ = λ { {γ} {a , b} -> refl*₁ A ,P T (∣ B ∣* (γ , a)) (trans*₂ B) (refl*₁ B) }
  ; refl*₂ = λ { {γ} {a , b} ->
      let BB = ∣ B ∣* (γ , fn (subst* A (R Γ γ)) a)
      in refl*₂ A ,P {!!} }
  ; trans*₁ = λ { {γ} {γ'} {γ''} {a , b} {p} {q} ->
    let BB = ∣ B ∣* (γ'' , fn (subst* A q) (fn (subst* A p) a))
    in trans*₁ A ,P T BB (trans*₂ B) (trans*₁ B) }
  ; trans*₂ = λ { {γ} {γ'} {γ''} {a , b} {p} {q} ->
    let BB = ∣ B ∣* (γ'' , fn (subst* A (T Γ p q)) a)
    in trans*₂ A ,P T BB (trans*₂ B) (trans*₂ B) }
  }

tm-to-sub : {A : Ty j Γ} -> Tm Γ A -> Γ ⟶ (Γ ︐ A)
tm-to-sub t = record
  { fn = λ γ → γ , tm t γ
  ; fn-rel = λ p → p ,P tm-rel t p
  }

pair : {A : Ty j Γ} {B : Ty k (Γ ︐ A)}
     -> (M : Tm Γ A) -> Tm Γ (B [ tm-to-sub M ]) -> Tm Γ (Sigma A B)
pair {A = A} {B} t s = record
  { tm = λ γ → tm t γ , tm s γ
  ; tm-rel = 
    λ {γ} {γ'} p →
      let BB = ∣ B ∣* (γ' , tm t γ')
      in tm-rel t p ,P T BB (trans*₂ B) (tm-rel s p)
  }

{-

hat : (A : Ty j (Γ ᵒᵖ)) -> Ty k (Γ ︐ᵒᵖ A) -> (γ : ∣ Γ ∣) -> Ty k (∣ A ∣* γ)
hat {Γ = Γ} A B γ = record
            { ∣_∣* = λ a → ∣ B ∣* (γ , a)
            ; subst* = λ x → subst* B (R Γ _ ,P T (∣ A ∣* γ) x (refl*₂ A))
            ; refl*₁ = λ {a} {b} → {!!}
            ; refl*₂ = {!!}
            ; trans*₁ = {!!}
            ; trans*₂ = {!!}
            }

Pi : (A : Ty j (Γ ᵒᵖ)) -> Ty k (Γ ︐ᵒᵖ A) -> Ty (j ⊔ k) Γ
Pi {Γ = Γ} A B = record
  { ∣_∣* = λ γ → record
    { ∣_∣ = Tm (∣ A ∣* γ) (hat {Γ = Γ} A B γ)
    ; _<_ = λ f g → (a : ∣ ∣ A ∣* γ ∣) -> _<_ (∣ B ∣* (γ , a)) (tm f a) (tm g a)
    ; R = λ _ _ → R (∣ B ∣* _) _
    ; T = λ p q a → let BB = (∣ B ∣* (γ , a)) in T BB (p a) (q a)
    }
  ; subst* = λ {γ γ'} p → record
    { fn = λ f -> record
      { tm = λ a → fn (subst* B (p ,P (R (∣ A ∣* γ) _))) (tm f (fn (subst* A p) a))
      ; tm-rel = λ {a₁} {a₂} q →
        let BB = ∣ B ∣* (γ' , a₂)
            pp = (p ,P R (∣ A ∣* γ) (fn (subst* A p) a₂))
        in T BB (trans*₂ B) (T BB (trans*₁ B)
             (fn-rel (subst* B pp) (tm-rel f (fn-rel (subst* A p) q))))
      }
    ; fn-rel = λ {f} {g} q a →
        fn-rel (subst* B (p ,P R (∣ A ∣* γ) _)) (q (fn (subst* A p) a))
    }
  ; refl*₁ = λ {γ} {f} a → tm-rel f (refl*₁ A {γ} {a})
  ; refl*₂ = λ {γ} {f} a →
      let BB = ∣ B ∣* (γ , a)
          aux = tm-rel f (refl*₂ A {γ} {a})
      in T BB (T BB (refl*₂ B) (trans*₁ B))
           (fn-rel (subst* B (R Γ _ ,P R (∣ A ∣* γ) _)) aux)
  ; trans*₁ = {!!}
  ; trans*₂ = {!!}
  }

-}
