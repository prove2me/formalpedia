-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_tail_support
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:35:28.674795+00:00
-- url     : https://prove2.me/theorems/c4b94905-9647-41ef-8bc4-afb44639d101
-- title:
--   Support bound for products of logarithmic tails
-- statement:
--   A nonzero coefficient of the product of logarithmic tails has degree at least the sum of each truncation order multiplied by its power. The inequality allows equality at the truncation cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hne : PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ)) ≠ 0) :
    (∑ i : Fin d.m,
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
        (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ) := by sorry
