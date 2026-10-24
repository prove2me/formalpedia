-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux_base
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_base
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:32:16.273128+00:00
-- url     : https://prove2.me/theorems/7dddff1d-375c-4805-8460-ec9872eb3d96
-- title:
--   Zero-dimensional unit simplex volume
-- statement:
--   The zero-dimensional simplex has volume 1. This handles the boundary case needed to start induction; the empty coordinate sum is 0 and the ambient zero-dimensional space has volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_base :
    MeasureTheory.volume
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin 0 => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by sorry
