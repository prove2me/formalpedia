-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_weighted
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_weighted
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:40:37.321996+00:00
-- url     : https://prove2.me/theorems/231ee670-7ee2-4580-b849-84880c3b46b1
-- title:
--   Weighted finite antidiagonal reindexing
-- statement:
--   For arbitrary coordinate weights, reindex the sum over finitely supported natural assignments with total k as a sum over functions into Fin (k + 1), retaining exactly those whose values sum to k.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_weighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ → ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
      ∏ i, w i (l i)) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, w i (f i).val
      else 0 := by sorry
