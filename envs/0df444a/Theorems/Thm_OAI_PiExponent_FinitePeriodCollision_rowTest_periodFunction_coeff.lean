-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_rowTest_periodFunction_coeff
-- name    : OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:25:05.730961+00:00
-- url     : https://prove2.me/theorems/c2e889ed-475d-4031-8783-be2c74514e69
-- title:
--   Cauchy row test recovers the period-function Taylor coefficient
-- statement:
--   For arbitrary complex scalar and center and natural exponents, the normalized radius-1/2 Cauchy row test of the period function equals the indicated formal coefficient. This isolates the analytic Taylor/Cauchy step from all integer-period simplifications. A proof route is to establish the power-series sum on `‖t‖ < 1`, use the corresponding `HasFPowerSeriesAt` at zero, and identify the Cauchy integral coefficient on the closed radius-1/2 disk. The pinned upstream `rowTest_periodFunction_eq_coeff` supplies this route.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
    (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (fun t => b * (1 + t) ^ h *
        (center + Complex.log (1 + t)) ^ d) =
      PowerSeries.coeff ell
        (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
          (PowerSeries.C center + PowerSeries.log ℂ) ^ d) := by sorry
