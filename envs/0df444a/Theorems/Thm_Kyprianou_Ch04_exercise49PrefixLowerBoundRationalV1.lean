-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixLowerBoundRationalV1
-- name    : Kyprianou.Ch04.exercise49PrefixLowerBoundRationalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:39.600715+00:00
-- url     : https://prove2.me/theorems/570a4d45-b70c-5d5d-ad73-029e1be03ec1
-- title:
--   A cadlag path lower bound on a compact prefix is equivalent to its rational samples and endpoint
-- statement:
--   A cadlag path lower bound on a compact prefix is equivalent to its rational samples and endpoint
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixLowerBoundRationalV1
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (s : NNReal) (b : ℝ) :
    (∀ u : NNReal, u ≤ s → b ≤ Y u) ↔
      b ≤ Y s ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < s →
        b ≤ Y (Real.toNNReal q) := by
  sorry
