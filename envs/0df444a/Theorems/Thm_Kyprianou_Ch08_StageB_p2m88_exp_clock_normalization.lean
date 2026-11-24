-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_normalization
-- name    : Kyprianou.Ch08.StageB.p2m88_exp_clock_normalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:58:23.960799+00:00
-- url     : https://prove2.me/theorems/1b76bae8-0bf3-400b-b8fb-8f9e2b1579ea
-- title:
--   Independent exponential clock normalization for nonnegative time rewards
-- statement:
--   Integrating any measurable nonnegative reward on nonnegative times against the discounted source time measure equals the reciprocal of the positive rate multiplied by the integral of the reward at the independent exponential clock.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, independent exponential killing.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Independent exponential clock normalization for nonnegative time rewards -/
theorem p2m88_exp_clock_normalization :
    ∀ q : ℝ, 0 < q → ∀ f : ℝ≥0 → ℝ≥0∞, Measurable f →
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * f t
        ∂positiveTimeLebesgue) =
      (ENNReal.ofReal q)⁻¹ * ∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q := by
  sorry

end Kyprianou.Ch08.StageB
