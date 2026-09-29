-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/5c42b4d0-e43b-5941-bd24-a3bf84a3a6f4
-- title:
--   Affine neighbourhood of a finite set from a translated affine open
-- statement:
--   Let $R$ be a commutative ring, $B$ a scheme and $g \colon B \to \operatorname{Spec} R$ a morphism, and let $LB$ be a relative group law on $g$: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$, a multiplication, a unit and an inversion on the set of $\varphi \colon T \to B$ with $\varphi \mathbin{;} g = t$, satisfying associativity, the two unit laws, the left inverse law, and compatibility of the multiplication with precomposition by any $\psi \colon T' \to T$ with $\psi \mathbin{;} t = t'$. Let $t_1 \colon T \to \operatorname{Spec} R$ be finite, flat, locally of finite presentation and surjective, and let $\gamma \colon T \to B$ satisfy $\gamma \mathbin{;} g = t_1$. Let $U$ be an affine open of $B$ and $S$ a finite set of points of $B$, and assume: for every field $K$ (in the ambient universe) and all $x \colon \operatorname{Spec} K \to B$, $t \colon \operatorname{Spec} K \to T$ with $x \mathbin{;} g = t \mathbin{;} t_1$, if the image of the closed point of $\operatorname{Spec} K$ under $x$ lies in $S$, then the image of that closed point under the morphism underlying the product, in $LB$ over $t \mathbin{;} t_1$, of $t$ followed by $\gamma$ with $x$ lies in $U$. Then there is an affine open $V$ of $B$ with $b \in V$ for every $b \in S$.
--
--   This is the translation step in the construction of an affine neighbourhood of a finite set of points on a scheme with a relative group law (as for Néron models and Jacobians): a hypothesis about left translates by $\gamma$ of the $K$-points over $S$ is converted into an affine open of $B$ containing $S$. It is used by the subsequent result which produces such an affine open from affineness, specialisation and Henselian hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of R))
    [IsFinite t₁] [Flat t₁] [LocallyOfFinitePresentation t₁] [Surjective t₁]
    (γ : SchemeHomOver t₁ g) (U : B.Opens) (hU : IsAffineOpen U) (S : Finset B)
    (hS : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B) (t : Spec (CommRingCat.of K) ⟶ T)
      (hx : x ≫ g = t ≫ t₁), x.base (IsLocalRing.closedPoint K) ∈ S →
      (LB.mul (t ≫ t₁) (schemeHomOverComp t rfl γ) ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by sorry
