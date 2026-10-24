-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_mul_volume
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:32:29.340682+00:00
-- url     : https://prove2.me/theorems/38db0cd6-cead-440f-a9ff-accd9e4ef32e
-- title:
--   Successor simplex volume from slicing and dilation
-- statement:
--   The volume of the unit simplex in n+1 coordinates is the n-coordinate unit simplex volume multiplied by 1/(n+1).

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
