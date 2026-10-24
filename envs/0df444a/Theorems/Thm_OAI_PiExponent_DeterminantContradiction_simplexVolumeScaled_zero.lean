-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:28:55.540849+00:00
-- url     : https://prove2.me/theorems/65016ef9-69f1-4698-a495-ab9acd521515
-- title:
--   Volume of the zero-dimensional simplex
-- statement:
--   In dimension zero, the region consists of the unique empty-coordinate vector, so its volume and the stated formula are both one for every nonnegative scale.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_zero (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ 0 / (Nat.factorial 0 : Real)) := by sorry
