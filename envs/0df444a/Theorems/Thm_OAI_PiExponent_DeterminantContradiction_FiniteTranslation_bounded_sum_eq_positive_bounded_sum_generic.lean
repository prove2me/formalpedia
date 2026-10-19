-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_bounded_sum_eq_positive_bounded_sum_generic
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:40:17.551007+00:00
-- url     : https://prove2.me/theorems/babd1206-ae5a-4a43-91f8-fa96c2fd128d
-- title:
--   Zero coordinates contribute nothing to bounded tuple sums
-- statement:
--   For a function vanishing at zero, restricting the bounded tuple sum to tuples with every coordinate positive does not change its value. The discarded tuples have a zero coordinate, hence a zero factor in their product.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
          (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i) := by sorry
