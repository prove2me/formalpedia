-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_slice_fubini
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_fubini
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:52:09.331985+00:00
-- url     : https://prove2.me/theorems/a8f6090b-0069-49a3-8306-84c55d0f05ce
-- title:
--   Simplex volume as an integral of its slices
-- statement:
--   Express the volume of the dimension-(n+1) standard simplex as the integral over its last coordinate of the volumes of the dimension-n fibers.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_fubini (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = (∫⁻ t in Set.Ioo (0 : Real) T, MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) := by sorry
