-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/200b3975-0fc1-5542-83d5-8fdf6ecf053f
-- title:
--   Abelian schemes over a ring are geometrically integral
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f\colon A \to \operatorname{Spec} R$ a morphism of schemes, and suppose that $f$ satisfies the property bundle `AbelianSchemePropertyBundle R f`, i.e. that $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(s)$ (the preimage of $\{s\}$ under the underlying continuous map of $f$) is a connected, non-empty subspace of $A$, and there exists a relative group law on $f$ in the sense of `RelativeGroupLaw R f`: for each scheme $T$ and each morphism $t\colon T \to \operatorname{Spec} R$, a multiplication, a unit element and an inversion on the set of $T$-points of $A$ over $\operatorname{Spec} R$ (morphisms $T \to A$ compatible with $t$ and $f$), satisfying associativity, the two unit laws and the left inverse law, and natural in the base in the sense that for $\psi\colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, composition with $\psi$ carries the multiplication for $t$ to the multiplication for $t'$. The conclusion is that $f$ is geometrically integral: for every field $K$ and every morphism $\operatorname{Spec} K \to \operatorname{Spec} R$, the fibre product $A \times_{\operatorname{Spec} R} \operatorname{Spec} K$ is an integral scheme.
--
--   This is the statement that an abelian scheme, in the axiomatic form used throughout the project (smooth, proper, connected fibres, relative group law), has geometrically integral fibres, now over an arbitrary commutative base ring rather than a field. It supplies the `GeometricallyIntegral` hypothesis required by the relative Picard and polarisation machinery and by the constructions of fake elliptic curves with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) : GeometricallyIntegral f := by sorry
