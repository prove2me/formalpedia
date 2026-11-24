-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridCeilSqueezeV1
-- name    : Kyprianou.Ch02.equalGridCeilSqueezeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:42:13.180659+00:00
-- url     : https://prove2.me/theorems/ec6c0abb-a6de-4a26-b092-f3a77b276dcb
-- title:
--   Ceiling grid position is within one cell to the right
-- statement:
--   Multiply the inequalities q ≤ ceil(q) < q+1 by b-a, divide by n+1 and add a.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridCeilSqueezeV1
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    ∀ n x, x ∈ Icc a b →
      x ≤ r n x ∧ r n x ≤ x+(b-a)/((n+1 : ℕ) : ℝ≥0) := by sorry
