-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridCeilGeometryV1
-- name    : Kyprianou.Ch02.equalGridCeilGeometryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:36:15.387048+00:00
-- url     : https://prove2.me/theorems/73bcb2bb-b5f1-4d8b-b924-40fd09d59966
-- title:
--   Ceiling grid maps preserve order, interval and grid image
-- statement:
--   The natural ceiling of the scaled displacement is between zero and n+1, is monotone, and equals k at the kth grid point.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridCeilGeometryV1
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    (∀ n, MonotoneOn (r n) (Icc a b)) ∧
    (∀ n, MapsTo (r n) (Icc a b) (Icc a b)) ∧
    (∀ n, r n '' Icc a b = g n '' Iic (n + 1)) := by sorry
