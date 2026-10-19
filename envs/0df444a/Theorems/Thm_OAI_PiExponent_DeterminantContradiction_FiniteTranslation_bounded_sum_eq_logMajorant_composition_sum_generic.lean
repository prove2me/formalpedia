-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_bounded_sum_eq_logMajorant_composition_sum_generic
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:35:05.619089+00:00
-- url     : https://prove2.me/theorems/ec28cf27-38de-4577-93f9-c170cf6c3a49
-- title:
--   Bounded tuple sums reduce to positive compositions
-- statement:
--   If f vanishes at zero, the bounded tuple sum of total k equals the sum over positive compositions of k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by sorry
