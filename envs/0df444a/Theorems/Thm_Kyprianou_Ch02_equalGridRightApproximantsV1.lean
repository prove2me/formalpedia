-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridRightApproximantsV1
-- name    : Kyprianou.Ch02.equalGridRightApproximantsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:33:20.632354+00:00
-- url     : https://prove2.me/theorems/270c4157-3db3-47fa-998c-b9d86bffe432
-- title:
--   Equal-grid ceiling maps approximate times from the right
-- statement:
--   For a=b use the constant map. Otherwise choose r_n(x) at the grid index ceil((x-a)(n+1)/(b-a)). Ceiling is monotone, fixes grid points and lies between x and x+(b-a)/(n+1).
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridRightApproximantsV1
    (a b : ℝ≥0) (hab : a ≤ b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    ∃ r : ℕ → ℝ≥0 → ℝ≥0,
      (∀ n, MonotoneOn (r n) (Icc a b)) ∧
      (∀ n, MapsTo (r n) (Icc a b) (Icc a b)) ∧
      (∀ n, r n '' Icc a b = g n '' Iic (n + 1)) ∧
      ∀ x ∈ Icc a b, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)) := by sorry
