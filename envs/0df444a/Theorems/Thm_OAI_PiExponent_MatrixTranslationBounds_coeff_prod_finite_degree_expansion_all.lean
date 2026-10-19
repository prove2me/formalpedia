-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion_all
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_all
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:23:16.096691+00:00
-- url     : https://prove2.me/theorems/8546a087-e20a-4a06-85b5-cd664d3aab7d
-- title:
--   Expand a product coefficient over all bounded degree assignments
-- statement:
--   Expand the coefficient of a finite product as a sum over all bounded degree assignments whose degrees sum to the target degree.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_all
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ f : ι → Fin (k + 1),
        if (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else 0 := by sorry
