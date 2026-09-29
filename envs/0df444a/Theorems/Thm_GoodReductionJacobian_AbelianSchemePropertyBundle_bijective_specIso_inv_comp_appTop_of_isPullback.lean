-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_specIso_inv_comp_appTop_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/94178187-c890-5e3f-ac5d-65522d23aae6
-- title:
--   Global functions on a base change of an abelian scheme
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} S$ be a morphism satisfying the bundle of properties `AbelianSchemePropertyBundle S f`, namely: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} S$ the fibre $f^{-1}(\{s\})$ of the underlying continuous map is connected (and non-empty), and there exists a relative group law for $f$ over $S$, i.e. a functorial multiplication, unit and inversion on the sets of $T$-points of $A$ over $\operatorname{Spec} S$, for all schemes $T$ over $\operatorname{Spec} S$, satisfying associativity, the unit laws and left inversion, and natural in $T$. Let $T$ be a commutative ring and $\varphi : S \to T$ a ring homomorphism, let $f' : A' \to \operatorname{Spec} T$ and $g : A' \to A$ be morphisms of schemes, and assume the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ is cartesian, so that $f'$ is the base change of $f$ along $\varphi$. Then the ring homomorphism $T \to \Gamma(A', \mathcal O_{A'})$ obtained by composing the inverse of the canonical isomorphism $T \cong \Gamma(\operatorname{Spec} T, \mathcal O)$ with the map on global sections induced by $f'$ is bijective.
--
--   This is the statement that $f_*\mathcal O_A = \mathcal O_{\operatorname{Spec} S}$ for an abelian scheme, in the form which persists under arbitrary base change: the global functions on every base change $A'$ of $A$ are exactly the scalars. It is used throughout the rigidity arguments for abelian schemes in the project, for instance in comparing polarisations and Rosati involutions after a faithfully flat base change and in recognising framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_specIso_inv_comp_appTop_of_isPullback
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f)
    {T : Type u} [CommRing T] (φ : S →+* T)
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of T)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ f'.appTop).hom := by sorry
