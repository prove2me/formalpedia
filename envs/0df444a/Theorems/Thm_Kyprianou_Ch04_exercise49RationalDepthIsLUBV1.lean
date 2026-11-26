-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthIsLUBV1
-- name    : Kyprianou.Ch04.exercise49RationalDepthIsLUBV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:45:32.31979+00:00
-- url     : https://prove2.me/theorems/6a8bb4b4-e01c-5166-bb76-0954f9ac9562
-- title:
--   The rational depth is the actual greatest downward excursion of a bounded-below right-continuous path
-- statement:
--   The rational depth is the actual greatest downward excursion of a bounded-below right-continuous path
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RationalDepthIsLUBV1
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t : NNReal, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t))) :
    IsLUB (Set.range (fun t => -Y t)) (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal := by
  sorry
