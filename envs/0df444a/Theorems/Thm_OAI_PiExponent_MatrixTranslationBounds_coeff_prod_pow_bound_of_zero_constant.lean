-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_pow_bound_of_zero_constant
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_pow_bound_of_zero_constant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:58:11.619+00:00
-- url     : https://prove2.me/theorems/6011cba0-734c-464d-9629-902e8f52188d
-- title:
--   Coefficient bound for finite products of zero-constant power series
-- statement:
--   For a finite family of complex power series with zero constant coefficients and all coefficients of norm at most one, every coefficient of their product with arbitrary natural-number multiplicities has norm at most 2 to its degree. The statement covers zero multiplicities and the empty product.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_pow_bound_of_zero_constant {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (m : σ → ℕ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (f i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, f i ^ (m i : ℕ))‖ ≤ (2 : ℝ) ^ k := by sorry
