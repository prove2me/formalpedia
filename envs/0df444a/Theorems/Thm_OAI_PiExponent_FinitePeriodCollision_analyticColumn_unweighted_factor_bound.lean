-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_unweighted_factor_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:27:18.531987+00:00
-- url     : https://prove2.me/theorems/7861891f-61f0-46c0-b8d8-d3576de4882e
-- title:
--   Unweighted growth bound for an analytic period column
-- statement:
--   Bound the analytic column by an exponential in the longitudinal parameter and the unweighted sum of its transverse exponents.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by sorry
