-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_finite_degree_sum_norm_bound
-- name    : OAI.PiExponent.MatrixTranslationBounds.finite_degree_sum_norm_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:20:25.088948+00:00
-- url     : https://prove2.me/theorems/c8321c57-7207-43c0-af65-64ecabbc94fb
-- title:
--   Bound the masked sum of coefficient product norms
-- statement:
--   Bound the sum of norms of the masked products over bounded degree assignments. Every valid term has norm at most 1, and the number of positive degree assignments totaling k is at most the stated binomial coefficient, including empty and impossible cases.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.finite_degree_sum_norm_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    (∑ f : ι → Fin (k + 1),
      ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else (0 : ℂ)‖) ≤ (Nat.choose k (Fintype.card ι) : ℝ) := by sorry
