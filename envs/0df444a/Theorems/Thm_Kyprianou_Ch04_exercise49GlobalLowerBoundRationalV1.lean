-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GlobalLowerBoundRationalV1
-- name    : Kyprianou.Ch04.exercise49GlobalLowerBoundRationalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:42.00296+00:00
-- url     : https://prove2.me/theorems/76714275-188e-5efd-ab23-8b1d3abbe12e
-- title:
--   A cadlag path lower bound on the entire half-line is equivalent to its positive rational samples
-- statement:
--   A cadlag path lower bound on the entire half-line is equivalent to its positive rational samples
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49GlobalLowerBoundRationalV1
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (b : ℝ) :
    (∀ u : NNReal, b ≤ Y u) ↔
      ∀ q : ℚ, 0 < q → b ≤ Y (Real.toNNReal q) := by
  sorry
