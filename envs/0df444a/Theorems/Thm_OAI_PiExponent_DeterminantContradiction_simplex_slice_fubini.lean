-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_fubini
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_fubini
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:07:58.0495+00:00
-- url     : https://prove2.me/theorems/915252c5-2646-426a-bd93-b1de70bda631
-- title:
--   Identify the slice integral with joint simplex volume
-- statement:
--   The integral of the slice volumes equals the volume of the joint region in which the slice coordinate and all simplex coordinates are nonnegative and their sum is below T.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_fubini (n : Nat) (T : Real) (hT : 0 < T) : (∫⁻ t in Set.Ioo (0 : Real) T, MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) = MeasureTheory.volume {z : Real × (Fin n → Real) | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T} := by sorry
