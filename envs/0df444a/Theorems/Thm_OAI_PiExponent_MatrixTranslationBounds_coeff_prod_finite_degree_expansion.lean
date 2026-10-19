-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion
-- name    : OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:20:10.21727+00:00
-- url     : https://prove2.me/theorems/8dbe3dcf-2a50-4396-9eb9-83b6cea36333
-- title:
--   Expand a product coefficient over bounded degree assignments
-- statement:
--   Expand the coefficient of the finite product as a sum over degree assignments bounded by k. Assignments with a zero degree vanish by the zero-constant-term hypothesis, and assignments whose degrees do not sum to k contribute zero.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ f : ι → Fin (k + 1),
        if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else 0 := by sorry
