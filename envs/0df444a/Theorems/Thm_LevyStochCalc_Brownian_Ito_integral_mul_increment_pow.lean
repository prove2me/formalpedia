-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow
-- name    : LevyStochCalc.Brownian.Ito.integral_mul_increment_pow
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:52:18.811227+00:00
-- url     : https://prove2.me/theorems/21b07763-18c5-4606-b32a-18648b7c2d1a
-- title:
--   integral mul increment pow
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_mul_increment_pow` is extracted from `LevyStochCalc.Brownian.ItoFourthMomentIncrements`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem _root_.LevyStochCalc.Brownian.Ito.integral_mul_increment_pow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by sorry
