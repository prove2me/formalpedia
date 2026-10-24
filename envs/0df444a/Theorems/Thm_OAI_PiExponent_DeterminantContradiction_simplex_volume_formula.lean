-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_formula
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:59:19.897746+00:00
-- url     : https://prove2.me/theorems/1d06cb39-23a4-43cd-b841-ef691357838e
-- title:
--   Volume formula for the standard simplex
-- statement:
--   The m-dimensional nonnegative simplex with coordinate sum strictly below T has ENNReal volume equal to the real value T^m/m! coerced to ENNReal. At m = 0, its volume is 1.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_formula (m : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = ENNReal.ofReal (T ^ m / (Nat.factorial m : Real)) := by sorry
