-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_compensated_second_moment
-- name    : LevyStochCalc.Poisson.Compensated.compensated_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:39:50.167682+00:00
-- url     : https://prove2.me/theorems/717e9615-db47-4c62-8e7e-b5643e8c663a
-- title:
--   compensated second moment
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.compensated_second_moment` is extracted from `LevyStochCalc.Poisson.CompensatedIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments and L²-isometry of the simple compensated-Poisson integral

The mean-zero / second-moment (variance) identities for the compensated Poisson
measure `Ñ(B) = N(B) − ν̂(B)`, and the diagonal / off-diagonal computation for
`simpleIntegral` (orthogonality of disjoint compensated-Poisson increments) that
they feed, culminating in the simple-integrand L²-isometry `simpleIntegral_isometry`
and L²-membership `simpleIntegral_memLp_compensated`. Builds on the integrand
definitions in `Poisson/CompensatedSimple.lean`.

This module carries the moment layer: the factorial-series identities
`∑' n, rⁿ / n! · n = r · exp r` and `∑' n, rⁿ / n! · n² = (r² + r) · exp r`, the mean,
second moment and variance of `poissonMeasure r` they give, and the transport of these
along `poisson_law` to `Ñ(B)`.

## Downstream modules

* `LevyStochCalc.Poisson.CompensatedIsometryOrthogonality` — the diagonal identity
  `∫⁻ ‖ξ_i · Ñ(B_i)‖² ∂P = ν̂(B_i) · ∫⁻ ‖ξ_i‖² ∂P` and the off-diagonal vanishing
  `∫ (ξ_i · Ñ(B_i)) · (ξ_j · Ñ(B_j)) ∂P = 0` for `i < j`.
* `LevyStochCalc.Poisson.CompensatedIsometryL2` — the Bochner expansion of
  `(∑_i ξ_i · Ñ(B_i))²`, the isometry `simpleIntegral_isometry` with its sum form, and
  the membership `simpleIntegral_memLp_compensated`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
theorem _root_.LevyStochCalc.Poisson.Compensated.compensated_second_moment
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal := by sorry
