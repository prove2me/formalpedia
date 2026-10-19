-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_geometry
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:24:25.684599+00:00
-- url     : https://prove2.me/theorems/b4f231e7-6800-4b74-8869-4fac56bca1d9
-- title:
--   Capacity and monotonicity of nonzero translation indices
-- statement:
--   Low translation indices have capacity lowIndexCount, all their weights are nonnegative, and a nonzero product of translation scalars has total index weight at least the total row weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) ∧
      (∀ f : Family d H, (∏ r : Row d H, scalar d r (f r)) ≠ 0 →
        (actualRowCount d H : ℝ) * H * actualMean d H ≤
          ∑ r : Row d H, weight d (f r).1) := by sorry
