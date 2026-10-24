-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_inverse_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inverse_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:14:17.965803+00:00
-- url     : https://prove2.me/theorems/47e3ceaa-c941-4927-88bf-b03bebad56c8
-- title:
--   Unit simplex volume is the inverse factorial
-- statement:
--   In every natural-number dimension, the volume of the nonnegative coordinate simplex whose coordinate sum is at most one equals the reciprocal of the dimension factorial. This removes the geometric volume computation from the parent; prove it by induction using last-coordinate sections and dilation of the lower-dimensional simplex.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inverse_factorial (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) := by sorry
