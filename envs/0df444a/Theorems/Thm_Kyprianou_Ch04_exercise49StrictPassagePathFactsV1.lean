-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49StrictPassagePathFactsV1
-- name    : Kyprianou.Ch04.exercise49StrictPassagePathFactsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:54:45.505258+00:00
-- url     : https://prove2.me/theorems/11724baa-9533-4f60-aab9-bfc21c08046d
-- title:
--   Before the first strict negative passage the path is nonnegative, and at finite passage it is nonpositive
-- statement:
--   Before the first strict negative passage the path is nonnegative, and at finite passage it is nonpositive
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49StrictPassagePathFactsV1
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (s : NNReal)
    (hs : (s : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t < 0}) :
    (∀ t : NNReal, t < s → 0 ≤ Y t) ∧ Y s ≤ 0 := by
  sorry
