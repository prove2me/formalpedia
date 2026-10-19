-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_content_closed_form
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_content_closed_form
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:51:15.016996+00:00
-- url     : https://prove2.me/theorems/bd9a3ebd-5938-4199-8a62-24c795f2b18d
-- title:
--   Closed form for nonnegative simplex volume
-- statement:
--   For every natural dimension and nonnegative radius, the simplex of nonnegative coordinates whose sum is at most the radius has volume equal to the radius to that dimension divided by the dimension factorial. The zero-dimensional and zero-radius cases are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_content_closed_form
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ r}).toReal =
      r ^ m / (Nat.factorial m : ℝ) := by sorry
