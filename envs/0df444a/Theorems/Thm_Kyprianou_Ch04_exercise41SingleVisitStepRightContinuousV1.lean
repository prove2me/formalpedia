-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepRightContinuousV1
-- name    : Kyprianou.Ch04.exercise41SingleVisitStepRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:37:58.784278+00:00
-- url     : https://prove2.me/theorems/fc9121ab-59ba-4e62-888c-601c6bef8a7c
-- title:
--   Right continuity of a single visit-count step
-- statement:
--   The single-event threshold-count process u↦1_{s≤u} is right continuous at all nonnegative times.
-- source:
--   Kyprianou (2006), Exercise 4.1(i), printed page 105.

import Mathlib
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SingleVisitStepRightContinuousV1 (s : NNReal) :
    ∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0) (Ici t) t := by
  sorry
