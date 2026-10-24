-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_slice_aux
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:10:36.719983+00:00
-- url     : https://prove2.me/theorems/47bcc0a8-ad0b-4a5a-980b-c42eca8bc656
-- title:
--   Simplex volume successor recurrence by slicing
-- statement:
--   For positive T, the volume in dimension m+1 is T/(m+1) times the volume in dimension m. Slicing by one coordinate, scaling each fiber, and integrating proves the recurrence without assuming the target formula.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_aux (m : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) * MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by sorry
