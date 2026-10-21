-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_budget_exponent
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_budget_exponent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:52:35.596301+00:00
-- url     : https://prove2.me/theorems/02483996-008a-4e0a-8917-b6f32ecb8153
-- title:
--   Column budget controls the growth exponent
-- statement:
--   Convert the weighted column budget into the target upper bound on the exponential growth exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_budget_exponent
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H) :
    Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by sorry
