-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:27:34.303672+00:00
-- url     : https://prove2.me/theorems/ff65e939-da64-42b7-a743-44738440df8f
-- title:
--   Closed form for the unit coordinate simplex volume
-- statement:
--   For every natural dimension `n`, the region of nonnegative vectors in `Fin n` whose coordinate sum is at most `1` has volume `1 / n!`. At `n = 0`, the region consists of the unique empty-coordinate vector and has volume `1`. This is the substantive volume calculation removed from the parent; an independent proof proceeds by slicing one coordinate, scaling the lower-dimensional simplex in each fiber, applying Fubini, and evaluating the integral of `(1 - t)^n`.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
