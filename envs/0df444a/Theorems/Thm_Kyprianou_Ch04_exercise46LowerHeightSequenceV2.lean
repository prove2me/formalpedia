-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46LowerHeightSequenceV2
-- name    : Kyprianou.Ch04.exercise46LowerHeightSequenceV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:48:27.848123+00:00
-- url     : https://prove2.me/theorems/fc890311-6bb2-4fdc-967c-8a23ef3f1423
-- title:
--   Measurable increasing positive heights approaching a positive level
-- statement:
--   Use max(y/2,y-1/(n+1)) for a positive level y.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46LowerHeightSequenceV2 :
    ∃ a : Nat → Real → Real, (∀ n, Measurable (a n)) ∧
      ∀ y : Real, 0 < y →
        (∀ n, 0 < a n y ∧ a n y < y) ∧
        Monotone (fun n => a n y) ∧
        Tendsto (fun n => a n y) atTop (nhds y) := by
  sorry
