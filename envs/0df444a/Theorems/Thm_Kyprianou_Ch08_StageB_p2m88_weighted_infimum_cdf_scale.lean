-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_weighted_infimum_cdf_scale
-- name    : Kyprianou.Ch08.StageB.p2m88_weighted_infimum_cdf_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:06:34.572809+00:00
-- url     : https://prove2.me/theorems/4779537c-1558-44f5-9dc1-765bf44a4c2f
-- title:
--   Exponentially weighted negative-infimum cumulative mass
-- statement:
--   The exponentially weighted cumulative mass of the source negative-infimum probability law at every real b is the nonnegative-real embedding of q/phi times the exponentially weighted scale value. The formula includes the atom at zero.
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

/-- Exponentially weighted negative-infimum cumulative mass -/
theorem p2m88_weighted_infimum_cdf_scale :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ) (w : ℝ → ℝ), 0 < φ → 0 < q → ν (Iio 0) = 0 →
      (∀ z : ℝ, z < 0 → w z = 0) →
      (∀ z : ℝ, 0 ≤ w z) →
      ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → cdf ν b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ b : ℝ,
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (q / φ * Real.exp (-φ * b) * w b) := by
  sorry

end Kyprianou.Ch08.StageB
