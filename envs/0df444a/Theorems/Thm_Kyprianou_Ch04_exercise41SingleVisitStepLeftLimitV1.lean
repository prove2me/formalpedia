-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepLeftLimitV1
-- name    : Kyprianou.Ch04.exercise41SingleVisitStepLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:37:59.311091+00:00
-- url     : https://prove2.me/theorems/e016a26f-6bc9-49dc-9cbd-407020ef8cf9
-- title:
--   Left limits of a single visit-count step
-- statement:
--   The single-event threshold-count process u↦1_{s≤u} has a finite left limit at each positive time.
-- source:
--   Kyprianou (2006), Exercise 4.1(i), printed page 105.

import Mathlib
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SingleVisitStepLeftLimitV1 (s : NNReal) :
    ∀ t : NNReal, 0 < t →
      ∃ l : ℝ, Tendsto
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0)
        (nhdsWithin t (Iio t)) (nhds l) := by
  sorry
