-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_degenerate_positive_composition_cut_code
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.degenerate_positive_composition_cut_code
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:25:00.753979+00:00
-- url     : https://prove2.me/theorems/16cf32e2-c2b8-4e5a-a068-2e5caada1747
-- title:
--   Inject positive compositions in degenerate cases
-- statement:
--   If q = 0, k = 0, or q = 1, the positive-composition subtype has at most one element and therefore admits an injective map into Finset (Fin k).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.degenerate_positive_composition_cut_code (q k : ℕ) (h : q = 0 ∨ k = 0 ∨ q = 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by sorry
