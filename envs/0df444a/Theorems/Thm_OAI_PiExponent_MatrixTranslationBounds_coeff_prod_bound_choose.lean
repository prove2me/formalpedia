-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_bound_choose
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_choose
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:11:45.126652+00:00
-- url     : https://prove2.me/theorems/faa1631d-382b-4857-90e4-78bfd87e48c6
-- title:
--   Coefficient bound by a binomial coefficient
-- statement:
--   The coefficient of degree k in the finite product is bounded by the binomial coefficient of k and the number of factors.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_choose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, g i)‖ ≤ (Nat.choose k (Fintype.card ι) : ℝ) := by
  sorry
