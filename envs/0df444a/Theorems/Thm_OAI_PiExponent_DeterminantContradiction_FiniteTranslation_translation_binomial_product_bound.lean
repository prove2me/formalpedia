-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_binomial_product_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:43:35.811956+00:00
-- url     : https://prove2.me/theorems/0aacb82f-e0cd-41ba-8b7c-52ef0e6c7c7a
-- title:
--   Binomial product bound by the translation index sum
-- statement:
--   The product of the two binomial coefficients at each coordinate is bounded by an exponential whose exponent is log 4 times the sum of the translation indices. The `Choice` bounds ensure the lower arguments fit the binomial tops; bound each coefficient by the corresponding power of 2 and aggregate over coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ)) := by sorry
