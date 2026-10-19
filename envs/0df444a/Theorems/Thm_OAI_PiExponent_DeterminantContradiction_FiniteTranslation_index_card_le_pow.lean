-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_card_le_pow
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_card_le_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:26:07.11774+00:00
-- url     : https://prove2.me/theorems/7751a336-e7e2-4ddd-9f29-4af2ba541ff2
-- title:
--   Finite translation index count bound
-- statement:
--   The number of weighted-simplex translation indices is at most (H+1) to the power m.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_card_le_pow
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Fintype.card (Index d H) : ℝ) ≤ (H + 1) ^ d.m := by sorry
