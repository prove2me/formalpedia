-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_aggregate_of_center_factor_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:26:19.164037+00:00
-- url     : https://prove2.me/theorems/760d3b56-c46a-405c-94ca-c66c7b058488
-- title:
--   Aggregate pointwise center bounds under the tail support budget
-- statement:
--   Aggregates the pointwise center estimates into the desired product estimate using the row and column simplex constraints, the explicit tail-support budget, and natural-subtraction boundary cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ))
    (hcenter :
      ∀ i : Fin d.m,
        ‖((r.1.val : ℂ) *
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
          Real.exp
            (Real.log (2 * (d.K : ℝ)) + nu -
              nu * MatrixArithmetic.logWeights (finiteDenominators d) i)) :
    ‖∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))‖ ≤
      Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by sorry
