-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallJumpContinuousQuadraticTailV1
-- name    : Kyprianou.Ch04.smallJumpContinuousQuadraticTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:12:36.534272+00:00
-- url     : https://prove2.me/theorems/4fe5f463-37f7-4b83-9498-630a0e10284a
-- title:
--   Continuous positive-cutoff Lévy quadratic tails vanish
-- statement:
--   For a two-sided Lévy measure the quadratic mass of absolute marks up to a positive real cutoff tends to zero as the cutoff decreases to zero. Use a reciprocal sequence and monotone comparison to obtain the full real-filter limit.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii), pp. 107–108

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem smallJumpContinuousQuadraticTailV1 (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Tendsto (fun r : ℝ => ∫⁻ z in {z : ℝ | |z| ≤ r},
      ENNReal.ofReal (z ^ 2) ∂ν) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  sorry
end Kyprianou.Ch04
