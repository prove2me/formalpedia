-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_clipped_cell_width
-- name    : Kyprianou.Ch04.ito43_cutoff_clipped_cell_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:06:21.317453+00:00
-- url     : https://prove2.me/theorems/48989f88-7da4-449d-8bac-1e460cb65c39
-- title:
--   Clipping a grid cell cannot enlarge its width
-- statement:
--   The uniform endpoints are monotone and their real difference is T divided by n. Taking the minimum with the stopping time contracts the interval.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_clipped_cell_width (T t : NNReal) (n k : ℕ) :
    let a := min t (T*(k:NNReal)/(n:NNReal))
    let b := min t (T*((k+1:ℕ):NNReal)/(n:NNReal))
    a ≤ b ∧ b ≤ t ∧ (b:ℝ)-(a:ℝ) ≤ (T:ℝ)/(n:ℝ) := by sorry
