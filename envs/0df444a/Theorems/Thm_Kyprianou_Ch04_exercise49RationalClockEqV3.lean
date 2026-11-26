-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockEqV3
-- name    : Kyprianou.Ch04.exercise49RationalClockEqV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:39:40.888329+00:00
-- url     : https://prove2.me/theorems/e11000b9-abab-4485-9222-fb144c2c88c7
-- title:
--   For a right-continuous real path nonnegative at zero, strict first passage equals its rational infimum
-- statement:
--   For a right-continuous real path nonnegative at zero, strict first passage equals its rational infimum
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RationalClockEqV3
    (Y : NNReal → ℝ) (h0 : 0 ≤ Y 0)
    (hrc : ∀ t : NNReal, ContinuousWithinAt Y (Ici t) t) :
    (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ Y t < 0}) =
      ⨅ q : ℚ, if 0 < (q : ℝ) ∧ Y (Real.toNNReal q) < 0 then
        (↑(Real.toNNReal q) : WithTop NNReal) else ⊤ := by
  sorry
