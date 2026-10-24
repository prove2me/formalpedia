-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_zero_aux
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:10:10.752698+00:00
-- url     : https://prove2.me/theorems/4bd4f48e-0110-4d94-9e2f-cf663ce688c9
-- title:
--   Zero-dimensional simplex volume auxiliary lemma
-- statement:
--   For positive T, the simplex in zero dimensions has volume one. Its constraint is satisfied by the unique function on Fin 0.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_aux (T : Real) (hT : 0 < T) : MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = ENNReal.ofReal (T ^ 0 / (Nat.factorial 0 : Real)) := by sorry
