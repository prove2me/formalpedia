-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_power_factor_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:27:57.867698+00:00
-- url     : https://prove2.me/theorems/366c4f4e-da12-4a3a-9db7-503d0205ed1d
-- title:
--   Transverse power growth bound
-- statement:
--   The norm of the transverse power, with truncated natural subtraction in its exponent, is bounded using the unweighted sum of the original exponents.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound
    {m : ℕ} (a A : Fin m → ℕ) {R : ℝ} (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖z ^ (∑ i, (a i - A i))‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by sorry
