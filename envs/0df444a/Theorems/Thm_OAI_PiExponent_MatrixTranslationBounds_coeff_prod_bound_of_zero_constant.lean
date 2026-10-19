-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_bound_of_zero_constant
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_of_zero_constant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:08:43.071842+00:00
-- url     : https://prove2.me/theorems/111190e0-fe61-4ab6-817f-077366619fb1
-- title:
--   Coefficient bound for finite products of zero-constant power series
-- statement:
--   For a finite family of complex power series with zero constant coefficient and coefficients of norm at most one, each coefficient of their product is bounded by 2 to its degree.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_of_zero_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, g i)‖ ≤ (2 : ℝ) ^ k := by
  sorry
