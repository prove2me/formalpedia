-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_truncated_exponential_cdf_identity
-- name    : Kyprianou.Ch08.StageB.p2m88_truncated_exponential_cdf_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:06:45.073072+00:00
-- url     : https://prove2.me/theorems/fcadaaf9-2b0e-46f8-8516-c74230aeab2b
-- title:
--   Truncated exponential integral by the distribution function
-- statement:
--   For any probability law supported on the nonnegative half-line, the exponential integral on the interval ending at b is the weighted CDF at b plus the integral of the CDF against the derivative of the exponential weight, including the boundary mass at zero.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, integration by parts of the negative-infimum law.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Truncated exponential integral by the distribution function -/
theorem p2m88_truncated_exponential_cdf_identity :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ b : ℝ), 0 < φ → 0 ≤ b → ν (Iio 0) = 0 →
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (Real.exp (-φ * b) * cdf ν b +
        φ * ∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * cdf ν t) := by
  sorry

end Kyprianou.Ch08.StageB
