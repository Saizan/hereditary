--------------------------------------------------------------------------------
-- This module implemented hereditary substitutions for the simply-typed      --
-- λ-calculus, now updated to the predicative polymorphic λ-calculus          --
--------------------------------------------------------------------------------

    -- This program is free software: you can redistribute it and/or modify
    -- it under the terms of the GNU General Public License as published by
    -- the Free Software Foundation, either version 3 of the License, or
    -- (at your option) any later version.

    -- This program is distributed in the hope that it will be useful,
    -- but WITHOUT ANY WARRANTY; without even the implied warranty of
    -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    -- GNU General Public License for more details.

    -- You should have received a copy of the GNU General Public License
    -- along with this program.  If not, see <http://www.gnu.org/licenses/>.

    -- Copyright Thorsten Altenkirch and Chantal Keller, 2010
    --   http://www.lix.polytechnique.fr/~keller/Recherche/hsubst.html
    -- Copyright Andrea Vezzosi, 2012
    --   https://github.com/Saizan/hereditary

module hsubst where

open import Data.Nat
open import Data.Fin hiding (_-_; _+_)

module Bruijn where

  -- De Bruijn contexts

  data Con<_> (A : Set) : Set where
    ε : Con< A >
    _,_ : Con< A > → A → Con< A >


  -- De Bruijn indices (the set of variables)

  data Var {A : Set} : Con< A > → A → Set where
    vz : forall {Γ σ} → Var (Γ , σ) σ
    vs : forall {τ Γ σ} → Var Γ σ → Var (Γ , τ) σ

  -- Removing a variable from a context

  _-_ : ∀ {A} {σ : A} → (Γ : Con< A >) → Var Γ σ → Con< A >
  ε       - ()
  (Γ , σ) - vz     = Γ
  (Γ , τ) - (vs x) = (Γ - x) , τ


  -- Conversely, adding a variable to a context (weakening)

  wkv : forall {A Γ σ τ} → (x : Var {A} Γ σ) → Var (Γ - x) τ → Var Γ τ
  wkv vz     y      = vs y
  wkv (vs x) vz     = vz
  wkv (vs x) (vs y) = vs (wkv x y)


  -- The equality between variables: the predicate...

  data EqV {A : Set}{Γ : Con< A >} : {σ τ : A} → Var Γ σ → Var Γ τ → Set where
    same : forall {σ} → {x : Var Γ σ} → EqV {A} {Γ} {σ} {σ} x x
    diff : forall {σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → EqV {A} {Γ} {σ} {τ} x (wkv x y)


  -- ... and the function that decides it

  eq : forall {A Γ σ τ} → (x : Var {A} Γ σ) → (y : Var Γ τ) → EqV x y
  eq vz      vz     = same
  eq vz      (vs x) = diff vz x
  eq (vs x)  vz     = diff (vs x) vz
  eq (vs x)  (vs y) with eq x y
  eq (vs .y) (vs y) | same = same
  eq (vs x) (vs .(wkv x y)) | diff .x y = diff (vs x) (vs y)

open Bruijn public

module Normal (n : ℕ) -- the number of primitive types
    where

  -- Simple types
  data STy : Set where
    κ : (i : Fin n) -> STy
    _⇒_ : STy → STy → STy

  -- Polymorphic types, HOAS style:
  -- (Π τ) being structurally larger than (τ σ) will guarantee termination 
  data Ty : Set where
    Π : (STy -> Ty) -> Ty
    _⇒_ : Ty -> Ty -> Ty
    κ : (i : Fin n) -> Ty

  embSTy : STy -> Ty
  embSTy (κ i) = (κ i)
  embSTy (t ⇒ t₁) = embSTy t ⇒ embSTy t₁

  Con = Con<_> Ty


  -- The set of normal forms

  mutual
  
    data Nf : Con → Ty → Set where
      λn   : forall {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
      Λn   : forall {Γ τ} → (∀ σ -> Nf Γ (τ σ)) → Nf Γ (Π τ)
      ne   : forall {Γ i} → Ne Γ (κ i) → Nf Γ (κ i)

    data Ne : Con → Ty → Set where
      _,_  : forall {Γ σ τ} → Var Γ σ → Sp Γ σ τ → Ne Γ τ
  
    data Sp : Con → Ty → Ty → Set where
      ε : forall {σ Γ} → Sp Γ σ σ
      _,_ : forall {Γ σ τ ρ} → (u : Nf Γ τ) → Sp Γ σ ρ → Sp Γ (τ ⇒ σ) ρ
      [_],_ : forall {Γ τ ρ} -> (σ : STy) -> Sp Γ (τ σ) ρ -> Sp Γ (Π τ) ρ


  -- Weakening of normal forms

  mutual
  
    wkNf : forall {σ Γ τ} → (x : Var Γ σ) → Nf (Γ - x) τ → Nf Γ τ
    wkNf x (λn t)        = λn (wkNf (vs x) t)
    wkNf x (Λn x₁) = Λn (λ σ → wkNf x (x₁ σ))
    wkNf x (ne (y , us)) = ne (wkv x y , wkSp x us)

    wkSp :  forall {σ Γ τ ρ} → (x : Var Γ σ) → Sp (Γ - x) τ ρ → Sp Γ τ ρ
    wkSp x ε        = ε
    wkSp x (u , us) = (wkNf x u) , (wkSp x us)
    wkSp x ([ σ₁ ], sp) = [ σ₁ ], wkSp x sp

    -- Add a normal form at the end of a spine

    appSp : forall {Γ σ τ ρ} → Sp Γ ρ (σ ⇒ τ) → Nf Γ σ → Sp Γ ρ τ
    appSp ε u = (u , ε)
    appSp (t , ts) u = ( t , appSp ts u)
    appSp ([ σ₁ ], sp) u = [ σ₁ ], appSp sp u

    appSpΠ : forall {Γ τ ρ} -> Sp Γ ρ (Π τ) -> ∀ σ → Sp Γ ρ (τ σ)
    appSpΠ ε σ = [ σ ], ε
    appSpΠ (u , sp) σ₁ = u , appSpΠ sp σ₁
    appSpΠ ([ σ ], sp) σ₁ = [ σ ], appSpΠ sp σ₁


  -- η-expansion of normal forms

  mutual

      nvar : forall {σ Γ} → Var Γ σ → Nf Γ σ
      nvar x = ne2nf (x , ε)

      ne2nf : forall {σ Γ} → Ne Γ σ → Nf Γ σ
      ne2nf {κ i}     xns      = ne xns
      ne2nf {(σ ⇒ τ)} (x , ns) = λn (ne2nf (vs x , appSp (wkSp vz ns) (nvar vz)))
      ne2nf {Π τ} (x , ns) = Λn (λ σ → ne2nf (x , appSpΠ ns σ))


  -- Hereditary substitutions: substitute a variable by a normal form and
  -- normalize the result

  mutual

      napp : forall {τ σ Γ} → Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
      napp (λn t) u = t [ vz := u ]
      
      _n[_] : ∀ {Γ τ} -> Nf Γ (Π τ) -> (σ : STy) -> Nf Γ (τ σ)
      Λn x n[ σ ] = x σ

      _[_:=_] : forall {σ Γ τ} → (Nf Γ τ) → (x : Var Γ σ) → Nf (Γ - x) σ → Nf (Γ - x) τ
      (λn t) [ x := u ] = λn (t [ (vs x) := (wkNf vz u) ])
      (ne (y , ts))          [ x := u ] with eq x y
      (ne (x , ts))          [ .x := u ] | same      = u ◇ (ts < x := u >)
      (ne (.(wkv x y'), ts)) [ .x := u ] | diff x y' = ne (y' , ts < x := u >)
      Λn x [ x₁ := u ] = Λn (λ σ → x σ [ x₁ := u ])

      _<_:=_> : forall {Γ σ τ ρ} → (Sp Γ τ ρ) → (x : Var Γ σ) → Nf (Γ - x) σ → Sp (Γ - x) τ ρ
      ε < x := u > = ε
      (t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)
      ([ σ₁ ], sp) < x := u > = [ σ₁ ], (sp < x := u >)

      -- apply a normal form to a spine

      _◇_ : forall {τ Γ σ} → Nf Γ σ → Sp Γ σ τ → Nf Γ τ
      t ◇ (u , us) = napp t u ◇ us
      t ◇ ε        = t
      t ◇ ([ σ ], us) = t n[ σ ] ◇ us

-- Normalization of a first order representation by conversion to Nf and back is omitted for brevity.
