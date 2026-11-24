-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_cdf_truncated_tonelli
-- name    : Kyprianou.Ch08.StageB.p2m88_cdf_truncated_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:31:15.435512+00:00
-- url     : https://prove2.me/theorems/cb9e0d4f-c737-421b-a7e0-1b0ecac2344b
-- title:
--   Truncated cumulative Laplace identity in ENNReal
-- statement:
--   Use the full cumulative Laplace identity for the law restricted to (-infinity,b] and split its cumulative integral at b. The endpoint contribution retains any atom at zero.
-- source:
--   Kyprianou (2006), Corollary 8.8, CDF integration by parts.

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_cdf_truncated_tonelli :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ b : ℝ), 0 < φ → 0 ≤ b → ν (Iio 0) = 0 →
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ*z)) ∂ν) =
      ENNReal.ofReal (Real.exp (-φ*b)) * ν (Iic b) +
        ENNReal.ofReal φ *
          (∫⁻ t in Ioc 0 b, ENNReal.ofReal (Real.exp (-φ*t)) * ν (Iic t)) := by
  sorry
end Kyprianou.Ch08.StageB
