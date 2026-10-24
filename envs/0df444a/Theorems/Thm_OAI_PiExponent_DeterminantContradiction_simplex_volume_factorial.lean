-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:22:59.438922+00:00
-- url     : https://prove2.me/theorems/65ddd5ac-6502-40a6-9fa6-01fafe8f3357
-- title:
--   Standard simplex volume
-- statement:
--   The n-dimensional standard simplex has volume 1/n!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_factorial (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
