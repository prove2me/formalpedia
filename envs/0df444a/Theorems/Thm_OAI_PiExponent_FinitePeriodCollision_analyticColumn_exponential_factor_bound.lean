-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_exponential_factor_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:27:38.045782+00:00
-- url     : https://prove2.me/theorems/9ce543d6-742c-46c2-ace6-164ede92b64a
-- title:
--   Exponential factor growth bound
-- statement:
--   The norm of the longitudinal complex exponential is bounded by the real exponential of h times the radius.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound
    (h : ℕ) {R : ℝ} (z : ℂ) (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp ((h : ℂ) * z)‖ ≤ Real.exp ((h : ℝ) * R) := by sorry
