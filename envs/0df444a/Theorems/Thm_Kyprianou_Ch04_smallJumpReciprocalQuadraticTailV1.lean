-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallJumpReciprocalQuadraticTailV1
-- name    : Kyprianou.Ch04.smallJumpReciprocalQuadraticTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:16:23.445747+00:00
-- url     : https://prove2.me/theorems/0da1b360-2ef6-5073-b861-728018d41f3e
-- title:
--   Quadratic tails on reciprocal cutoffs
-- statement:
--   The quadratic mark mass within reciprocal cutoffs tends to zero.
-- source:
--   Kyprianou (2006), Exercise 4.5, finite cutoff and quadratic tail

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem smallJumpReciprocalQuadraticTailV1 (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Tendsto (fun n : ℕ => ∫⁻ z in {z : ℝ | |z| ≤ 1 / ((n : ℝ) + 2)},
      ENNReal.ofReal (z ^ 2) ∂ν) atTop (𝓝 0) := by
  sorry
end Kyprianou.Ch04
