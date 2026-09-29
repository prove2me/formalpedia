-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mul_comp_eq_mul_of_isPullback_of_one_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.mul_comp_eq_mul_of_isPullback_of_one_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d1f7eac6-b92b-5cf1-82e8-76ee44651c49
-- title:
--   Comparison map intertwines group laws with matching unit sections
-- statement:
--   Let $\varphi : R \to R'$ be a ring homomorphism between commutative rings, let $f : A \to \operatorname{Spec} R$ and $f' : A' \to \operatorname{Spec} R'$ be morphisms of schemes, and let $g_A : A' \to A$ be a morphism making the square with sides $g_A$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ cartesian (`IsPullback`). Let $L$ be a relative group law on $f$ and $L'$ one on $f'$: that is, each assigns to every test morphism $t$ to the base a multiplication, a unit and an inversion on the set of $t$-points (morphisms from the test scheme to $A$, resp. $A'$, composing with the structure morphism to $t$), satisfying associativity, both unit laws, left inverses, and naturality of the multiplication under composition of test morphisms. Assume the bundle `AbelianSchemePropertyBundle` for $f'$, i.e. $f'$ is smooth and proper, each fibre $f'^{-1}\{s\}$ of the underlying map of spaces is connected, and relative group laws on $f'$ exist. Assume the unit sections correspond: the unit of $L'$ at the identity of $\operatorname{Spec} R'$ followed by $g_A$ equals $\operatorname{Spec}(\varphi)$ followed by the unit of $L$ at the identity of $\operatorname{Spec} R$. Then for every $t' : T \to \operatorname{Spec} R'$ and all $t'$-points $x, y$ of $A'$, the product $x \cdot_{L'} y$ followed by $g_A$ equals the $L$-product, over $t'$ followed by $\operatorname{Spec}(\varphi)$, of $x$ followed by $g_A$ and $y$ followed by $g_A$.
--
--   This is the rigidity statement that a comparison map across a cartesian square of abelian schemes which matches the identity sections is a homomorphism for the relative group laws, here in the functor-of-points formulation used for group laws in this development. It is used in the construction of framed polarised abelian schemes, namely in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_mul_comp_eq_mul_of_isPullback_of_one_comp_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.mul_comp_eq_mul_of_isPullback_of_one_comp_eq
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (gA : A' ⟶ A) (hgA : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R' f') (hA' : AbelianSchemePropertyBundle R' f')
    (hone : (L'.one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ gA =
      Spec.map (CommRingCat.ofHom φ) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f') :
    (L'.mul t' x y).1 ≫ gA =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨x.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, y.2]⟩).1 := by sorry
