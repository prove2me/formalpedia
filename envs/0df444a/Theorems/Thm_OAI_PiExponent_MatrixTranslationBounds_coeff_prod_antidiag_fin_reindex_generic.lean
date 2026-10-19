-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_generic
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_generic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:44:09.004358+00:00
-- url     : https://prove2.me/theorems/c6cc4f05-33a5-43a8-a890-372753a74475
-- title:
--   Generic finite antidiagonal reindexing
-- statement:
--   For any complex-valued summand on natural-valued assignments, reindex the sum over the finite antidiagonal of total k by functions into Fin (k + 1), discarding functions whose values do not sum to k.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℕ) → ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k, φ l) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        φ (fun i => (f i).val)
      else 0 := by
  sorry
