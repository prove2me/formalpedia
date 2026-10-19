-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_row_card_factorization
-- name    : OAI.PiExponent.DeterminantContradiction.row_card_factorization
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T23:15:48.359256+00:00
-- url     : https://prove2.me/theorems/30056b0e-85e6-4d93-8e62-82c90be33c6d
-- title:
--   Factorization of the strict row count
-- statement:
--   The row type is the product of `Fin K` and the strict weighted simplex, so its cardinality is K times the simplex cardinality. This equality holds for every real H, including cutoffs at which the simplex is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.row_card_factorization
    {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ) :
    OAI.PiExponent.DeterminantContradiction.actualRowCount d H = d.K *
      (OAI.PiExponent.strictWeightedSimplex
        (OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
          (OAI.PiExponent.MatrixArithmetic.logWeights
            (OAI.PiExponent.DeterminantContradiction.finiteDenominators d))) H).card := by sorry
