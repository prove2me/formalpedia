-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_expansion_and_card
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.expansion_and_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:24:10.627303+00:00
-- url     : https://prove2.me/theorems/7ca5efcc-c3fa-4367-a774-afc4e2610fba
-- title:
--   Finite translation expansion and polynomial entropy bound
-- statement:
--   The actual determinant expands over the finite translation families. Their number is at most the real translation envelope raised to the number of rows.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.expansion_and_card
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det = (∑ f : Family d H, term d selection f) ∧
      (Fintype.card (Family d H) : ℝ) ≤
        translationEnvelope d.m d.v0 H ^ actualRowCount d H := by sorry
