-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_zero_ENNReal
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_ENNReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:30:45.547363+00:00
-- url     : https://prove2.me/theorems/d3044243-cc1b-4980-b88d-f21999866674
-- title:
--   Zero-dimensional simplex volume
-- statement:
--   The zero-dimensional nonnegative coordinate simplex has volume one, equal to the reciprocal of zero factorial.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_ENNReal :
    MeasureTheory.volume
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin 0 => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by sorry
