-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_equiv
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_equiv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:00:42.166145+00:00
-- url     : https://prove2.me/theorems/07f2e049-e0d9-4867-bc68-49f19fee064a
-- title:
--   Antidiagonal assignments as bounded coordinate functions
-- statement:
--   There is an equivalence between finitely supported natural assignments on the antidiagonal of total k and functions into Fin (k + 1) whose coordinate values total k; the equivalence preserves every coordinate value.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_equiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ e :
      {l : ι →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k} ≃
      {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k},
      ∀ l i, ((e l).1 i).val = l.1 i := by
  sorry
