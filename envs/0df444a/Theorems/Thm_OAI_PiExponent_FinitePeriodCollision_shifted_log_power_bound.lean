-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_shifted_log_power_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.shifted_log_power_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T08:13:01.494978+00:00
-- url     : https://prove2.me/theorems/744696ce-6294-40b9-8982-e2bc89f1e72c
-- title:
--   Half-radius bound for logarithmic row weights
-- statement:
--   On the integration circle for `rowTest`, the translated logarithmic argument divided by `R` has norm at most one half, so its `d`th power contributes `(1/2)^d` and the row functional contributes `2^ell`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.shifted_log_power_bound
    (center : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell
      (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by sorry
