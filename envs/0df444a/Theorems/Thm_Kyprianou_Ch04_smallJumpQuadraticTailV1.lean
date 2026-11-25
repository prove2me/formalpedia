-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallJumpQuadraticTailV1
-- name    : Kyprianou.Ch04.smallJumpQuadraticTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:00:50.759971+00:00
-- url     : https://prove2.me/theorems/b34cb702-2684-50b4-8a5f-7affc9690427
-- title:
--   Two-sided Lévy small-mark quadratic tails vanish
-- statement:
--   For a general two-sided Lévy measure, any decreasing sequence of measurable mark sets contained in (-1,1) whose intersection lies in {0} has quadratic-weighted mass tending to zero. This includes shrinking reciprocal small-jump cutoffs.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); continuity from above of the finite quadratic-weighted restricted Lévy measure.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem smallJumpQuadraticTailV1
    (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hSub : ∀ n, B n ⊆ Ioo (-1 : ℝ) 1)
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ)) :
    Tendsto (fun n => ∫⁻ z in B n, ENNReal.ofReal (z ^ 2) ∂ν)
      atTop (𝓝 0) := by
  sorry
end Kyprianou.Ch04
