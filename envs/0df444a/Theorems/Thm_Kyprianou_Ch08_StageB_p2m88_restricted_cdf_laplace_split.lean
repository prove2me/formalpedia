-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_restricted_cdf_laplace_split
-- name    : Kyprianou.Ch08.StageB.p2m88_restricted_cdf_laplace_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:31:21.504994+00:00
-- url     : https://prove2.me/theorems/e0050fb5-c191-45fd-bfd2-ee5ed11c0889
-- title:
--   Split the cumulative Laplace integral of a truncated measure
-- statement:
--   The cumulative mass of the restriction to (-infinity,b] agrees with the original cumulative mass up to b and is constant thereafter.
-- source:
--   Kyprianou (2006), Corollary 8.8, CDF integration by parts.

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_restricted_cdf_laplace_split :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (φ b : ℝ), 0 < φ → 0 ≤ b →
      (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-φ*t)) *
        (ν.restrict (Iic b)) (Iic t)) =
      (∫⁻ t in Ioc 0 b, ENNReal.ofReal (Real.exp (-φ*t)) * ν (Iic t)) +
        ENNReal.ofReal (Real.exp (-φ*b) / φ) * ν (Iic b) := by
  sorry
end Kyprianou.Ch08.StageB
