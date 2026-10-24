-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:57:33.739858+00:00
-- url     : https://prove2.me/theorems/2b1e9707-d8e2-4a86-9ceb-7ac7c2683a3a
-- title:
--   Zero-dimensional unit simplex volume
-- statement:
--   The simplex in the zero-dimensional coordinate space has volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_zero :
    MeasureTheory.volume
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal 1 := by sorry
