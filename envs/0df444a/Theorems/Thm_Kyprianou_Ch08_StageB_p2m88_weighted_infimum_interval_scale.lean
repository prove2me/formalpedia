-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_weighted_infimum_interval_scale
-- name    : Kyprianou.Ch08.StageB.p2m88_weighted_infimum_interval_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:01:01.00317+00:00
-- url     : https://prove2.me/theorems/a8a603ff-668b-46c9-b34c-6893a6ec1709
-- title:
--   Weighted infimum interval mass from its scale CDF
-- statement:
--   Exponentially weighting the given probability law yields an interval mass equal to q/phi times the difference of the exponentially weighted scale values. The half-open interval includes the atom at zero when its left endpoint is negative.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7 and Corollary 8.8, integration by parts in the exponential-clock law.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Weighted infimum interval mass from its scale CDF -/
theorem p2m88_weighted_infimum_interval_scale :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ) (w : ℝ → ℝ), 0 < φ → 0 < q → ν (Iio 0) = 0 →
      (∀ z : ℝ, z < 0 → w z = 0) →
      (∀ z : ℝ, 0 ≤ w z) →
      ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → cdf ν b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ a b : ℝ, a ≤ b →
      (∫⁻ z in Ioc a b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (q / φ *
        (Real.exp (-φ * b) * w b - Real.exp (-φ * a) * w a)) := by
  sorry

end Kyprianou.Ch08.StageB
