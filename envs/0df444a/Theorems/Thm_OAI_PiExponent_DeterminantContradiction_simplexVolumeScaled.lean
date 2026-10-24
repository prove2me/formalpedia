-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:24:12.311824+00:00
-- url     : https://prove2.me/theorems/6079e146-b721-4fe4-ab6e-a7e3a7e34825
-- title:
--   Volume of a scaled standard simplex
-- statement:
--   For every dimension and nonnegative scale, the nonnegative simplex with coordinate sum at most that scale has volume r^n/n!, including dimension zero and scale zero.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n / (Nat.factorial n : Real)) := by sorry
