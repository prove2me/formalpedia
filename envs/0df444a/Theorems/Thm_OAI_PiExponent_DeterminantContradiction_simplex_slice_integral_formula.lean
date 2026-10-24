-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_formula
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:59:33.577847+00:00
-- url     : https://prove2.me/theorems/273f95dd-1100-4fe2-9606-7ce277bca803
-- title:
--   Integral of the standard simplex slice volumes
-- statement:
--   The lintegral of the n-dimensional simplex slice volumes over 0 < t < T is T^(n+1)/(n+1)! coerced to ENNReal.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_formula (n : Nat) (T : Real) (hT : 0 < T) : (∫⁻ t in Set.Ioo (0 : Real) T, MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) = ENNReal.ofReal (T ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
