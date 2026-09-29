-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/1e601e95-5dcb-5831-aec0-0ee60d44d222
-- title:
--   Smooth group law over a local ring has constant relative dimension
-- statement:
--   Let $R$ be a commutative ring that is local, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is assumed smooth. Suppose $f$ carries a relative group law in the following sense: for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} R$ there are operations $\mathrm{mul}$, $\mathrm{one}$ and $\mathrm{inv}$ on the set of $T$-points of $X$ over $t$, that is on pairs consisting of a morphism $T \to X$ together with a proof that it followed by $f$ equals $t$; these operations satisfy associativity, left and right unit laws and left inverse cancellation for each such $t$, and multiplication is natural in the base: for any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, composing with $\psi$ takes the product of two $T$-points over $t$ to the product of their composites, viewed as $T'$-points over $t'$. The conclusion is that there exists a natural number $d$ such that $f$ is smooth of relative dimension $d$, in Mathlib's sense `SmoothOfRelativeDimension d f`.
--
--   This is the standard fact that a smooth group scheme over a local base has a well-defined relative dimension: the relative dimension of a smooth morphism is locally constant, it is constant on each fibre by homogeneity under the group law, and the base is connected since $R$ is local. It serves as a basic dimension-theoretic input for the treatment of abelian schemes, Néron models and Jacobians of good reduction in the project, and is used in the construction and comparison of fake elliptic curves and their deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [Smooth f]
    (G : RelativeGroupLaw R f) :
    ∃ d : ℕ, SmoothOfRelativeDimension d f := by sorry
