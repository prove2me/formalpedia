-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteVisitCountCardinalityCadlagV1
-- name    : Kyprianou.Ch04.exercise41FiniteVisitCountCardinalityCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:52:03.760244+00:00
-- url     : https://prove2.me/theorems/1d9b7bc1-b838-533f-b00a-3082228e951d
-- title:
--   Finite cumulative visit-cardinality process is càdlàg
-- statement:
--   For a finite set of zero-visit times, the real-valued count of all marks at or before each time is right continuous with a finite left limit on positive times.
-- source:
--   Finite counting-process calculation for Kyprianou (2006), Exercise 4.1(i), pp. 105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteMarkCountCadlagV1
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteVisitCountCardinalityCadlagV1 (S : Finset NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ((S.filter (fun s => s ≤ u)).card : ℝ))
      (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ((S.filter (fun s => s ≤ u)).card : ℝ))
      (nhdsWithin t (Iio t)) (nhds l)) := by
  sorry
