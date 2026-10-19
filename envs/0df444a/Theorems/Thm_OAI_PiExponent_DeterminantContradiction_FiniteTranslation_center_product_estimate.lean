-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_estimate
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_estimate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T13:35:36.761857+00:00
-- url     : https://prove2.me/theorems/e33385b7-52e1-4116-97c7-190ddadc40af
-- title:
--   Approximation-center product estimate
-- statement:
--   Bound the product of the approximation-center powers in `scalar`, allowing the explicit center-side error `H * (nu / d.F0 + log 2 / v0)`. The finite choice ensures each exponent is nonnegative. This removes the approximation-center estimate from the parent; a proof route uses the approximation inequality in `FixedData`, the complex norm of `2 * I * (p/q - π)`, and the weighted bounds on the selected index and row. The truncation-tail issue is not part of this child.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_estimate
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖∏ i : Fin d.m,
      ((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))‖ ≤
      Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + Real.log 2 / (d.v0 : ℝ))) := by sorry
