-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_coeff_le_majorant
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_le_majorant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:45:16.527263+00:00
-- url     : https://prove2.me/theorems/97b9d57b-2b96-4dca-afc3-cc1c540ae97e
-- title:
--   A truncated logarithmic tail is coefficientwise bounded by the positive logarithmic majorant
-- statement:
--   For every truncation order and degree, the absolute value of the logarithmic-tail coefficient is at most the coefficient of the series with coefficients 1/n in positive degrees. Below the truncation cutoff the tail coefficient is zero; at and above the cutoff its magnitude is 1/n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_le_majorant (N n : ℕ) :
    ‖PowerSeries.coeff n
      ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)‖ ≤
    ‖PowerSeries.coeff n
      (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹))‖ := by sorry
