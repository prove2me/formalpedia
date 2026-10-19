-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_composition_reciprocal_sum_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_composition_reciprocal_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:20:04.879417+00:00
-- url     : https://prove2.me/theorems/78d815ba-6063-431a-9a9f-8c6715791040
-- title:
--   Reciprocal composition sum bounded by its indexing cardinality
-- statement:
--   The norm of the finite sum of reciprocal products indexed by positive q-tuples summing to k is at most the number of such tuples. Positivity of every coordinate makes each reciprocal factor have norm at most one; the finite-sum triangle inequality then gives the bound, including empty-index and q = 0 cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_composition_reciprocal_sum_bound (q k : ℕ) :
    ‖(∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹))‖ ≤
      ((logMajorantCompositions q k).card : ℝ) := by sorry
