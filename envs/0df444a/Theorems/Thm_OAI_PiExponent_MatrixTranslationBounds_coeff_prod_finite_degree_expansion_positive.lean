-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion_positive
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_positive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:23:31.182665+00:00
-- url     : https://prove2.me/theorems/20b7c83c-4c7d-4d76-875d-ceffd59590db
-- title:
--   Remove zero-degree assignments from the product coefficient expansion
-- statement:
--   Under zero constant terms, the bounded degree assignment sum is unchanged when assignments with a zero coordinate are removed.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0) :
    (∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0) =
    ∑ f : ι → Fin (k + 1),
      if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0 := by sorry
