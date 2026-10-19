-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_binomial_factor_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:39:53.052178+00:00
-- url     : https://prove2.me/theorems/1ea7b4ab-3e5f-4a37-8a5d-d526c25e2264
-- title:
--   Weighted binomial product bound for a translation choice
-- statement:
--   The product of binomial factors attached to an admissible row and choice is bounded by the exponential allowance involving log 4 and the minimum weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar)) := by sorry
