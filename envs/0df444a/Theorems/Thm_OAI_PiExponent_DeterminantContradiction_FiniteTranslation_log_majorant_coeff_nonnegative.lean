-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_coeff_nonnegative
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_coeff_nonnegative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:45:49.473759+00:00
-- url     : https://prove2.me/theorems/54e1263c-5034-45fd-bddc-d67508156296
-- title:
--   The positive logarithmic majorant has nonnegative real coefficients
-- statement:
--   Each coefficient of the majorant series is a nonnegative real: it is zero in degree zero and 1/n in positive degree. This supplies the positivity needed for coefficientwise product majorization.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_coeff_nonnegative (n : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n
        (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹)) = (x : ℂ) := by sorry
