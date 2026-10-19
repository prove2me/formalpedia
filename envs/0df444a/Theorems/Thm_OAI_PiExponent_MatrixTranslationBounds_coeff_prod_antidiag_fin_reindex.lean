-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:36:55.474985+00:00
-- url     : https://prove2.me/theorems/ed31a7f4-be61-4e5c-ba6c-92781424f46e
-- title:
--   Reindex a finitely supported antidiagonal by finite degree assignments
-- statement:
--   Reindex the sum over finitely supported natural degree assignments with total k as a sum over all functions into `Fin (k + 1)`, retaining exactly the assignments whose values sum to k. The correspondence preserves each coefficient product, including when k is zero or the index type is empty.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
      ∏ i, PowerSeries.coeff (l i) (g i)) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0 := by sorry
