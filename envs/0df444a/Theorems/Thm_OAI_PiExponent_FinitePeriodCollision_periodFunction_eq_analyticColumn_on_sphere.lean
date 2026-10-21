-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodFunction_eq_analyticColumn_on_sphere
-- name    : OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:25:41.564994+00:00
-- url     : https://prove2.me/theorems/5aeee7af-704e-44b6-8606-68eb29bb6e8c
-- title:
--   Cancel the integer period shift on the Cauchy circle
-- statement:
--   On the radius-1/2 circle, the period function with center `j·2πi` equals the specified analytic column. The circle bound ensures `1+t` is nonzero; `exp (j·2πi) = 1` and `exp (log (1+t)) = 1+t` then identify the exponential factor with `(1+t)^h`. The argument also covers zero total exponent and empty products.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      (((∏ i, (a i).choose (A i) : ℕ) : ℂ) * (1 + t) ^ h *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ (∑ i, (a i - A i))) =
        analyticColumn h a A
          ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            Complex.log (1 + t)) := by sorry
