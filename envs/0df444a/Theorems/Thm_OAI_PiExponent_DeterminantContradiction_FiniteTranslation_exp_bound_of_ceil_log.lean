-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_exp_bound_of_ceil_log
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:30:06.38837+00:00
-- url     : https://prove2.me/theorems/53c007d7-ca66-48db-8fd9-c4374b07280c
-- title:
--   Ceiling-rounded logarithmic denominator allowance
-- statement:
--   For positive approximation denominator q and scale K, replacing the logarithmic denominator by its ceiling is covered by the additive nu allowance in the exponential.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
    {nu : ℝ} (q K : ℕ) (hnu : 0 ≤ nu)
    (hq : 2 ≤ q) (hK : 1 ≤ K) :
    2 * (K : ℝ) * (q : ℝ) ^ (-nu) ≤
      Real.exp
        (Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ)) := by sorry
