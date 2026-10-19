-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_subtype
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_subtype
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:50:28.582985+00:00
-- url     : https://prove2.me/theorems/625c408a-e29d-4d4e-9d78-8966157e03eb
-- title:
--   Antidiagonal reindexing as subtype sums
-- statement:
--   Reindex the subtype sum over natural-valued finitely supported functions on the antidiagonal of total k as a sum over functions into Fin (k + 1) whose coordinate values total k, preserving any summand depending on the underlying assignment.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_subtype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℕ) → ℂ) (k : ℕ) :
    (∑ l : {l : ι →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k}, φ l.1) =
    ∑ f : {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k},
      φ (fun i => (f.1 i).val) := by
  sorry
