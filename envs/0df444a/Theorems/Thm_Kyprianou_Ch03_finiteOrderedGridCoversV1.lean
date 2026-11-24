-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteOrderedGridCoversV1
-- name    : Kyprianou.Ch03.finiteOrderedGridCoversV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:22:51.987859+00:00
-- url     : https://prove2.me/theorems/32d75ad4-dfcf-4390-865a-a7ce0713eb9b
-- title:
--   Ordered finite grid covering prescribed bounded nonnegative times
-- statement:
--   Sort the finite set of prescribed times after adjoining zero. Its cardinality is positive; use its increasing finite enumeration. The first time is zero and all times are bounded by t.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parent rawReversalFiniteCylinderV1 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.finiteOrderedGridCoversV1
    (t : NNReal) (J : Finset {s : NNReal // s ≤ t}) :
    ∃ n : Nat, ∃ q : Fin (n + 1) → NNReal,
      Monotone q ∧ q 0 = 0 ∧ (∀ i, q i ≤ t) ∧
      ∀ s ∈ J, ∃ i, q i = (s : NNReal) := by sorry
