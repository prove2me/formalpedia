-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finsupp_antidiag
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finsupp_antidiag
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:36:41.739319+00:00
-- url     : https://prove2.me/theorems/4380cea0-d5d8-437c-92a7-8b58a71e4591
-- title:
--   Expand a product coefficient over a finitely supported antidiagonal
-- statement:
--   Mathlib’s coefficient formula for a finite product, specialized to the universal finite index set, expresses the coefficient as a sum over finitely supported degree assignments whose total is the target degree.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finsupp_antidiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
        ∏ i, PowerSeries.coeff (l i) (g i) := by sorry
