-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepCadlagV1
-- name    : Kyprianou.Ch04.exercise41SingleVisitStepCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:34:41.483557+00:00
-- url     : https://prove2.me/theorems/cb034074-7643-40f5-963f-6da693587994
-- title:
--   Right continuity and left limits of an individual visit-count jump
-- statement:
--   For every nonnegative mark s, the cumulative threshold step u ↦ 1_{s≤u} is right continuous on the time half-line and has a finite left limit at every positive time.
-- source:
--   Deterministic counting process underpinning Kyprianou (2006), Exercise 4.1(i), printed pp. 105–106.

import Mathlib
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- The cumulative step for a single visit has right continuity and a left limit. -/

theorem Kyprianou.Ch04.exercise41SingleVisitStepCadlagV1 (s : NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0) (Ici t) t) ∧
    (∀ t : NNReal, 0 < t →
      ∃ l : ℝ, Tendsto
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0)
        (nhdsWithin t (Iio t)) (nhds l)) := by
  sorry
