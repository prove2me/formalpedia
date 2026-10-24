-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_slice
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:41:10.355102+00:00
-- url     : https://prove2.me/theorems/34c4ae8d-9d01-47ec-9ae7-7b45be4ae938
-- title:
--   Slice identity for the unit simplex volume
-- statement:
--   Assuming the n-dimensional closed unit simplex has volume 1/n!, express the (n+1)-dimensional volume as that value multiplied by the interval integral of (1−t)^n from 0 to 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal
        ((1 / (Nat.factorial n : Real)) *
          (∫ t in (0 : Real)..1, (1 - t) ^ n)) := by sorry
