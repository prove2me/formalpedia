-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridCeilIndexBoundsV1
-- name    : Kyprianou.Ch02.equalGridCeilIndexBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:42:14.187048+00:00
-- url     : https://prove2.me/theorems/0fed12d7-fd7d-402c-b32c-d3f1e72410a0
-- title:
--   Ceiling index is bounded and fixes each grid index
-- statement:
--   Bound the scaled displacement by n+1, then use natural ceiling monotonicity. On any grid point the scaled displacement equals its natural index exactly.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridCeilIndexBoundsV1
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let q : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      (x-a)*((n+1 : ℕ) : ℝ≥0)/(b-a)
    (∀ n x, x ∈ Icc a b → ⌈q n x⌉₊ ≤ n+1) ∧
    ∀ n k, ⌈q n (g n k)⌉₊ = k := by sorry
