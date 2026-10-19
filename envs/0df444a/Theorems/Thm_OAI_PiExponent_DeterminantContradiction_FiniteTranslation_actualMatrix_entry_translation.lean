-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_actualMatrix_entry_translation
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actualMatrix_entry_translation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:21:26.843226+00:00
-- url     : https://prove2.me/theorems/ac1b06e9-1691-4a1d-9c14-93006e5196e3
-- title:
--   Exact finite translation expansion of an actual matrix entry
-- statement:
--   Every actual matrix entry equals its finite translation sum, with the center errors and exact truncation tails incorporated into the scalar factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actualMatrix_entry_translation
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (c : Column d H) :
    actualMatrix d H r c =
      ∑ t : Choice d H r, scalar d r t *
        PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
          ((periodModel r.1.val (c.1 0) (fun i => c.1 i.succ)).coeff
            (InterpolationMatrix.exponentVector t.1.1)) := by sorry
