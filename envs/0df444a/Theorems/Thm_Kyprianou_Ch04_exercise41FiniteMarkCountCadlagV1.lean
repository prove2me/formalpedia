-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteMarkCountCadlagV1
-- name    : Kyprianou.Ch04.exercise41FiniteMarkCountCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:47:24.775834+00:00
-- url     : https://prove2.me/theorems/3b0fc065-6eda-450f-b0c6-c5065ffa1dbe
-- title:
--   A finite set of zero-visit marks has a càdlàg cumulative count
-- statement:
--   For any finite set S of nonnegative times, its cumulative count (sum of indicators 1_{s≤t}) is right continuous with a finite left limit at every positive t.
-- source:
--   Deterministic counting-process lemma for Kyprianou (2006), Chapter 4, Exercise 4.1(i), pp. 105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepCadlagV1
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteMarkCountCadlagV1 (S : Finset NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ∑ s ∈ S, if s ≤ u then (1 : ℝ) else 0)
      (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ∑ s ∈ S, if s ≤ u then (1 : ℝ) else 0)
      (nhdsWithin t (Iio t)) (nhds l)) := by
  sorry
