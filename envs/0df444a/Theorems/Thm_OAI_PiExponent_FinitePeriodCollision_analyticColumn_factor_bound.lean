-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_factor_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:52:12.840359+00:00
-- url     : https://prove2.me/theorems/29d8829c-1eb7-46e5-b110-0c9aee201899
-- title:
--   Factor growth bound for analytic period columns
-- statement:
--   Bound the analytic column by an exponential with separate contributions from the longitudinal exponent and the weighted transverse exponents.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_factor_bound
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R wstar : ℝ}
    (hR : 1 ≤ R) (hws : 0 < wstar) (hw : ∀ i, wstar ≤ w i)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) := by sorry
