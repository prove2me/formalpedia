-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:06:31.925029+00:00
-- url     : https://prove2.me/theorems/63ecaf37-fb4b-4940-ba07-2f9c004fcc03
-- title:
--   Zero-dimensional simplex factorial formula
-- statement:
--   The zero-dimensional unit simplex is the singleton in `Fin 0 → ℝ`, whose volume is `1 = 1/0!`.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_zero :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by sorry
