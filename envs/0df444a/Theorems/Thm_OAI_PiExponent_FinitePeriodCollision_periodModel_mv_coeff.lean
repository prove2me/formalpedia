-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodModel_mv_coeff
-- name    : OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:15:41.566416+00:00
-- url     : https://prove2.me/theorems/2294f89d-37b6-43a1-bcaf-941d17eb29be
-- title:
--   Multivariate coefficient of the period model
-- statement:
--   The coefficient of the multivariate period model at exponent vector A is the period factor times the product, over coordinates, of the binomial coefficient and the shifted-log power. If a coordinate exponent exceeds its available degree, the coefficient and the corresponding binomial factor are both zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    (periodModel j h a).coeff (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h *
        ∏ i, (PowerSeries.C ((j : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)) +
          PowerSeries.log ℂ) ^ (a i - A i) := by sorry
