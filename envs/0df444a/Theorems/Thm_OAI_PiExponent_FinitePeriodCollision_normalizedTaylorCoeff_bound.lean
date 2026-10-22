-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_normalizedTaylorCoeff_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.normalizedTaylorCoeff_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:12:42.657416+00:00
-- url     : https://prove2.me/theorems/e2cd8950-6e0d-4b87-988f-9abe86bccf53
-- title:
--   Bound on normalized Taylor coefficients
-- statement:
--   Cauchy's integral formula bounds each Taylor coefficient normalized by the radius by the supremum bound on the radius-`R` circle.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.normalizedTaylorCoeff_bound
    (f : ℂ → ℂ) (R : NNReal) (hR : 0 < R) (D : ℝ)
    (hD : ∀ z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f z‖ ≤ D)
    (d : ℕ) :
    ‖cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ))‖ ≤ D := by sorry
