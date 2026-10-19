-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_positive_bounded_sum_eq_logMajorant_composition_sum_generic
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:40:33.843379+00:00
-- url     : https://prove2.me/theorems/0ad6b240-92ab-4e57-8efd-8703c0241e4f
-- title:
--   Positive bounded tuples reindex as compositions
-- statement:
--   The sum over positive bounded tuples of total `k` equals the sum over `logMajorantCompositions`, by the coordinatewise coercion map and its inverse on positive tuples of total `k`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic (q k : ℕ) (f : ℕ → ℂ) :
    (∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
        (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by sorry
