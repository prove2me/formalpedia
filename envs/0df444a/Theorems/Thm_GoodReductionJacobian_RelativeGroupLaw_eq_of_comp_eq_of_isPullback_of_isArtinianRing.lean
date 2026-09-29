-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c58dd662-b479-5f5d-906d-66ebefe4f911
-- title:
--   Rigidity over an Artinian local base for group-scheme targets
-- statement:
--   Let $R$ be an Artinian local ring, $k_0$ a field, and $\pi\colon R\to k_0$ a surjective ring homomorphism. Let $f\colon A\to\operatorname{Spec}R$ be a proper flat morphism of schemes, and let $f'\colon A'\to\operatorname{Spec}R$ be a morphism equipped with a relative group law $L'$, i.e. for every scheme $T$ and every $t\colon T\to\operatorname{Spec}R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi\colon T\to A' \mid \varphi\circ\text{(over)}\;\varphi \text{ followed by } f' = t\}$, satisfying associativity, the two unit laws and left inverse, and compatible with composition: for $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ carries products to products. Let $f_0\colon A_0\to\operatorname{Spec}k_0$ be a morphism whose map on global sections $k_0\to\Gamma(A_0,\mathcal O_{A_0})$ is bijective, and let $i\colon A_0\to A$ make the square with $f_0$, $f$ and $\operatorname{Spec}\pi$ a pullback square, so $A_0$ is the closed fibre of $f$. Let $s\colon\operatorname{Spec}R\to A$ be a section of $f$. Then any two morphisms $e_1,e_2\colon A\to A'$ over $\operatorname{Spec}R$ (that is, $e_j$ followed by $f'$ equals $f$) which agree after precomposition with $i$ and after precomposition with $s$ are equal.
--
--   This is the infinitesimal form of the rigidity lemma for morphisms into a group scheme: over an Artinian local base, a morphism from a proper flat scheme whose closed fibre satisfies $H^0(A_0,\mathcal O_{A_0})=k_0$ into a scheme with a relative group law is determined by its restriction to the closed fibre together with its value along one section. It is used in the construction and comparison of fake elliptic curves with level structure in the Čerednik–Drinfeld part of the argument, for instance to show that lifts of a homomorphism of closed fibres and actions on deformations are unique.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    {k₀ : Type u} [Field k₀] (π : R →+* k₀) (hπ : Function.Surjective π)
    {A A' A₀ : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [IsProper f] [Flat f]
    {f' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R f')
    {f₀ : A₀ ⟶ Spec (CommRingCat.of k₀)} (hf₀ : Function.Bijective f₀.appTop)
    (i : A₀ ⟶ A) (hi : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s : Spec (CommRingCat.of R) ⟶ A) (hs : s ≫ f = 𝟙 _)
    (e₁ e₂ : A ⟶ A') (he₁ : e₁ ≫ f' = f) (he₂ : e₂ ≫ f' = f)
    (h : i ≫ e₁ = i ≫ e₂) (hs' : s ≫ e₁ = s ≫ e₂) : e₁ = e₂ := by sorry
