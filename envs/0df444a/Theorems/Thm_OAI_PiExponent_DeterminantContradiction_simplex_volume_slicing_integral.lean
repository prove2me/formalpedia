-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_slicing_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:45:14.305845+00:00
-- url     : https://prove2.me/theorems/4c404351-b956-43c3-963d-6ef180fc24e6
-- title:
--   Fubini and scaling formula for nonnegative simplices
-- statement:
--   For every natural dimension n and positive real radius r, the volume of the nonnegative simplex in dimension n+1 equals the dimension-n unit simplex volume multiplied by the integral of (r−t)^n over [0,r]. Prove this independently by coordinate slicing, Fubini, and dilation of Lebesgue measure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing_integral
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ r}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal *
        (∫ t in (0 : ℝ)..r, (r - t) ^ n) := by sorry
