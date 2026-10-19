-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_nontrivial_positive_composition_cut_code
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.nontrivial_positive_composition_cut_code
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:25:21.646822+00:00
-- url     : https://prove2.me/theorems/26541077-d128-4fe7-940e-867612fb16c9
-- title:
--   Encode nontrivial positive compositions by cuts
-- statement:
--   For q,k > 0 with q ≠ 1, positive q-tuples summing to k inject into subsets of Fin k by recording the proper partial sums minus one. Ordering the resulting cuts recovers the partial sums and then the tuple entries.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.nontrivial_positive_composition_cut_code (q k : ℕ) (hq : 0 < q) (hk : 0 < k) (hqne : q ≠ 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by sorry
