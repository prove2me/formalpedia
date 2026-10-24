-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:48:43.094985+00:00
-- url     : https://prove2.me/theorems/b61db0af-4dd0-4614-96f0-1c5ab2ae2352
-- title:
--   Zero-dimensional simplex volume
-- statement:
--   For positive height, the zero-dimensional simplex has volume one.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_zero (T : Real) (hT : 0 < T) : MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = ENNReal.ofReal (T ^ 0 / (Nat.factorial 0 : Real)) := by sorry
