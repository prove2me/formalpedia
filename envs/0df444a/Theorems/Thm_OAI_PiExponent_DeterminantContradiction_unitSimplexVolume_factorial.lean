-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:24:15.928409+00:00
-- url     : https://prove2.me/theorems/0df91cea-b403-49fa-93a5-01e48d43e798
-- title:
--   Closed form for the unit coordinate simplex volume
-- statement:
--   For each natural number n, the region of nonnegative vectors in Fin n whose coordinate sum is at most 1 has volume 1 divided by n factorial. This includes n = 0, where the empty-coordinate region has volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
