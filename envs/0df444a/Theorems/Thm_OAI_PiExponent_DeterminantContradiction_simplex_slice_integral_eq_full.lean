-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_eq_full
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_full
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:55:03.011629+00:00
-- url     : https://prove2.me/theorems/b0341f0a-0504-43f5-b2a6-d5f904bb1137
-- title:
--   Extend the slice integral to all real parameters
-- statement:
--   The integral over the open interval of slice volumes equals the lower integral over all real parameters of the joint region's fiber volumes. Outside the interval the fiber is empty, except possibly at the null endpoint t = 0.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_full (n : Nat) (T : Real) (hT : 0 < T) : (∫⁻ t in Set.Ioo (0 : Real) T, MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) = (∫⁻ t : Real, MeasureTheory.volume {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) := by sorry
