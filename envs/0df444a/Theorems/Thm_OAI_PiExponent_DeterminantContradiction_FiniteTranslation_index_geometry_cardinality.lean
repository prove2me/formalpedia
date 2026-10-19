-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_geometry_cardinality
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:55:55.89663+00:00
-- url     : https://prove2.me/theorems/a43e9071-6307-4c25-b550-048e0e54438c
-- title:
--   Finite simplex cardinality and weight bounds
-- statement:
--   The low-height weighted simplex is nonempty; every index has nonnegative weight; and the indices at height H whose weights are at most A·H are counted by at most the low-height simplex cardinality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) := by sorry
