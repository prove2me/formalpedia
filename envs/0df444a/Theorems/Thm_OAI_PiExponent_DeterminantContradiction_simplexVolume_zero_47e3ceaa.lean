-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_47e3ceaa
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_47e3ceaa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:21:52.998906+00:00
-- url     : https://prove2.me/theorems/59bd68c1-f264-45a9-bea5-1d1a24d641eb
-- title:
--   Zero-dimensional simplex volume
-- statement:
--   The zero-dimensional unit simplex has volume one, equal to the reciprocal of 0!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_47e3ceaa :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial 0 : Nat) : Real)) := by sorry
