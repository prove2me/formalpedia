-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d0ae2f59-36ec-52d0-b409-24c7d9e84dfa
-- title:
--   Uniqueness of a relative group law compatible with base change
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $\iota : \operatorname{Spec} R' \to \operatorname{Spec} R$ be a morphism of schemes, and let $f : A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$. Suppose $G$ is a relative group law on $f$, that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $\varphi : T \to A$ with $\varphi \circ\!\!\text{-after-} f = t$ (the set written `SchemeHomOver t f`), subject to associativity, the two unit laws, left invertibility, and compatibility with precomposition by any $\psi : T' \to T$ with $t \circ \psi = t'$. Let $L_1, L_2$ be relative group laws on the second projection $A \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$. Assume that for $i = 1, 2$, for every scheme $T$, every $t' : T \to \operatorname{Spec} R'$ and all $P, Q$ over $t'$, the first projection applied after the $L_i$-product of $P$ and $Q$ equals the underlying morphism of the $G$-product, over $t'$ followed by $\iota$, of the first projections of $P$ and of $Q$. Then $L_1 = L_2$ as relative group laws.
--
--   This is the uniqueness half of the statement that a relative group law descends along base change: a group law on the fibre product whose first projection is a homomorphism for the given law on $A$ is unique. It is used in the construction of canonical polarisation data for fake elliptic curves, where compatible group laws on base changes and thickenings must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (L₁ L₂ : RelativeGroupLaw R' (pullback.snd f ι))
    (h₁ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₁.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h₂ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₂.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    L₁ = L₂ := by sorry
