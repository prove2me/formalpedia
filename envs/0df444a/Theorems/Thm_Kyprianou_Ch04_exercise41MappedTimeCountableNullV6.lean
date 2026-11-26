-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41MappedTimeCountableNullV6
-- name    : Kyprianou.Ch04.exercise41MappedTimeCountableNullV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:22:25.082819+00:00
-- url     : https://prove2.me/theorems/2eafcdb7-f01c-4052-962e-9dee1250cf78
-- title:
--   Countable time sets are null for the image of restricted Lebesgue measure
-- statement:
--   Countable time sets are null for the image of restricted Lebesgue measure
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41MappedTimeCountableNullV6
    (T : NNReal) (S : Set NNReal) (hS : S.Countable) :
    ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).map Real.toNNReal) S = 0  := by
  sorry
