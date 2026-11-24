-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_discounted_time_integral_limit
-- name    : Kyprianou.Ch08.StageB.p2m88_discounted_time_integral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:41:45.511808+00:00
-- url     : https://prove2.me/theorems/059cce7a-0645-4b00-981e-857eb81d78ac
-- title:
--   Monotone convergence of the discounted time integral
-- statement:
--   For a decreasing sequence of discounts tending to zero, the exponential discount factors increase pointwise to one. Monotone convergence yields the limit of the time integral, including an infinite limiting integral.
-- source:
--   Kyprianou (2006), Corollary 8.8, zero-discount limit.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_discounted_time_integral_limit :
    ∀ (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ≥0∞), Measurable f →
      ∀ r : ℕ → ℝ, Antitone r → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-r n*(t : ℝ))) * f t ∂μ)
        atTop (nhds (∫⁻ t : ℝ≥0, f t ∂μ)) := by
  sorry
end Kyprianou.Ch08.StageB
