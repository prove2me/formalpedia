-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_coeff_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:40:09.828005+00:00
-- url     : https://prove2.me/theorems/49110251-8a92-483d-9613-037fc6b4d9fd
-- title:
--   Coefficient bound for a product of truncated logarithmic tails
-- statement:
--   The selected coefficient of the product of logarithmic tails is bounded by the exponential allowance involving log 2 and the row’s zeroth-coordinate weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by sorry
