-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_masked_sum_le_valid_card
-- name    : OAI.PiExponent.MatrixTranslationBounds.masked_sum_le_valid_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:34:17.70446+00:00
-- url     : https://prove2.me/theorems/9ccc8409-af83-49c2-8bd4-2f18dfd2dfaf
-- title:
--   Bound a masked coefficient sum by its valid assignment count
-- statement:
--   The masked sum is at most the number of assignments satisfying the positivity and total-degree conditions. Each valid product has norm at most 1 by the coefficient bound.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.masked_sum_le_valid_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    [DecidablePred (fun f : ι → Fin (k + 1) => (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k)]
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    (∑ f : ι → Fin (k + 1),
      ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else (0 : ℂ)‖) ≤
      (Fintype.card {f : ι → Fin (k + 1) //
        (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k} : ℝ) := by sorry
