-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_norm_le
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_norm_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:38:38.750778+00:00
-- url     : https://prove2.me/theorems/b822879c-cebf-4676-9fdf-fb47b11fe741
-- title:
--   Weighted exponential growth bound for transverse period columns
-- statement:
--   A positive weighted column budget bounds every transverse entire column uniformly on the closed disk of radius R, for R at least one, independently of the transverse exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_norm_le
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by sorry
