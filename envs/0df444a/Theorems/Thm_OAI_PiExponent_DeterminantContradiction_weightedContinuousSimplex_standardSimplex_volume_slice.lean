-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_slice
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:49:05.105708+00:00
-- url     : https://prove2.me/theorems/76f5d977-1b49-4675-b653-8481caddfe43
-- title:
--   Successor simplex slice formula
-- statement:
--   Given the dimension-`n` volume formula at every positive height, slicing a dimension-`n+1` simplex by one coordinate expresses its volume as the integral of the lower-dimensional slice volumes.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_slice (n : Nat) (T : Real) (hT : 0 < T) (ih : ∀ s : Real, 0 < s → MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < s} = ENNReal.ofReal (s ^ n / (n.factorial : Real))) : MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = (∫⁻ t in Set.Ioo (0 : Real) T, ENNReal.ofReal ((T - t) ^ n / (n.factorial : Real)) ∂MeasureTheory.volume) := by sorry
