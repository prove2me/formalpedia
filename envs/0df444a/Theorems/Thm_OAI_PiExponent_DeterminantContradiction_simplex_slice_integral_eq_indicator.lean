-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_eq_indicator
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_indicator
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:01:49.582434+00:00
-- url     : https://prove2.me/theorems/bf639214-1e81-41a8-832b-00be157ce567
-- title:
--   Rewrite the interval integral using an indicator
-- statement:
--   The lintegral over the open interval equals the all-real lintegral of the slice-volume function multiplied by the interval indicator.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_indicator (n : Nat) (T : Real) (hT : 0 < T) : (∫⁻ t in Set.Ioo (0 : Real) T, MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) = (∫⁻ t : Real, Set.indicator (Set.Ioo (0 : Real) T) (fun u : Real => MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - u}) t ∂MeasureTheory.volume) := by sorry
