-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FloorCellV4
-- name    : Kyprianou.Ch04.exercise41FloorCellV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:23:21.909703+00:00
-- url     : https://prove2.me/theorems/1eec8336-0347-4a3c-8145-77f3cadfb56f
-- title:
--   A half-open block has a canonical floor-indexed cell
-- statement:
--   A half-open block has a canonical floor-indexed cell
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FloorCellV4
    (a h s : ℝ) (n : ℕ) (hh : 0 < h)
    (ha : a ≤ s) (hb : s < a + (n : ℝ) * h) :
    let i := Nat.floor ((s - a) / h)
    i ∈ Finset.range n ∧ a + (i : ℝ) * h ≤ s ∧
      s < a + ((i : ℝ) + 1) * h  := by
  sorry
