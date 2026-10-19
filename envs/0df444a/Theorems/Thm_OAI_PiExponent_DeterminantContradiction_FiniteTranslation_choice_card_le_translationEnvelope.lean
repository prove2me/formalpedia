-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_choice_card_le_translationEnvelope
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_translationEnvelope
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:21:42.135051+00:00
-- url     : https://prove2.me/theorems/a33bb642-369b-40d6-a82b-5e59cedae056
-- title:
--   Polynomial envelope for one row's finite translation choices
-- statement:
--   For each actual row at positive height, the number of finite translation choices is at most the translation envelope.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_translationEnvelope
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (Fintype.card (Choice d H r) : ℝ) ≤
      translationEnvelope d.m d.v0 H := by sorry
