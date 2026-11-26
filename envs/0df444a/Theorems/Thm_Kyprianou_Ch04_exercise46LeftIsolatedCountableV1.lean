-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46LeftIsolatedCountableV1
-- name    : Kyprianou.Ch04.exercise46LeftIsolatedCountableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:33.491794+00:00
-- url     : https://prove2.me/theorems/e6bf1d61-194e-4da4-aab9-d32e8a04d52f
-- title:
--   Left-isolated level sets are countable
-- statement:
--   The left-neighbourhood filter within the set is trivial at each point; use the countability of one-sided isolated points in a second-countable ordered space.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46LeftIsolatedCountableV1
    (S : Set NNReal)
    (h : ∀ t ∈ S, ∃ a : NNReal, a < t ∧
      ∀ u ∈ S, a < u → u < t → False) :
    S.Countable := by
  sorry
