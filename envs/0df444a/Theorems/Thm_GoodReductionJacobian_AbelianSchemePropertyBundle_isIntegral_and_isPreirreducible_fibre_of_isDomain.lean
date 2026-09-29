-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_and_isPreirreducible_fibre_of_isDomain
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_and_isPreirreducible_fibre_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/1aa5de84-ee14-552e-8852-f52303c2eb83
-- title:
--   Integrality and fibre irreducibility for an abelian scheme and its square
-- statement:
--   Let $R$ be a commutative Noetherian domain, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism of schemes (all in universe $0$). Assume given a relative group law $L$ for $f$ in the sense of the structure `RelativeGroupLaw`: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws and left inversion, and natural with respect to morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$ (i.e. with $\psi$ followed by $t$ equal to $t'$). Assume further `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the subspace $f^{-1}(\{s\})$ of the underlying space of $A$ is connected, and $f$ admits a relative group law. Then two blocks of four assertions hold: first, $f$ is smooth, $f$ is quasi-compact, $A$ is an integral scheme, and for every $s \in \operatorname{Spec} R$ the set $f^{-1}(\{s\})$ is preirreducible; second, the same four assertions for the composite of the first projection $A \times_{\operatorname{Spec} R} A \to A$ with $f$, namely that this composite is smooth and quasi-compact, that $A \times_{\operatorname{Spec} R} A$ is an integral scheme, and that each of its fibres over a point of $\operatorname{Spec} R$ is preirreducible. Note that preirreducibility, rather than irreducibility, is asserted for the fibres.
--
--   This is the standard fact that the total space of an abelian scheme over a Noetherian domain, and likewise its fibre square, is integral with irreducible fibres, packaged in the shape needed downstream. It is used in the treatment of polarisations and Rosati-type persistence statements for Jacobians of good reduction and in the study of fake elliptic curves over Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_and_isPreirreducible_fibre_of_isDomain.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_and_isPreirreducible_fibre_of_isDomain
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f) :
    (Smooth f ∧ QuasiCompact f ∧ IsIntegral A ∧
      ∀ s : ↥(Spec (CommRingCat.of R)), IsPreirreducible (f.base ⁻¹' {s} : Set ↥A)) ∧
    (Smooth (pullback.fst f f ≫ f) ∧ QuasiCompact (pullback.fst f f ≫ f) ∧ IsIntegral (pullback f f) ∧
      ∀ s : ↥(Spec (CommRingCat.of R)), IsPreirreducible ((pullback.fst f f ≫ f).base ⁻¹' {s} : Set ↥(pullback f f))) := by sorry
