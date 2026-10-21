-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_binomial_product_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:27:23.96007+00:00
-- url     : https://prove2.me/theorems/495e5d84-b579-4258-844a-d637fd58d77a
-- title:
--   Binomial product growth bound
-- statement:
--   The complex norm of the product of binomial coefficients is bounded by the exponential of the sum of the exponents times log 2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound
    {m : ℕ} (a A : Fin m → ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log 2) := by sorry
