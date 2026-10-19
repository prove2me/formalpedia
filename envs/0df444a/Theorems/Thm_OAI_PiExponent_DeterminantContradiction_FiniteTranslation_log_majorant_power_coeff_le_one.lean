-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_le_one
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_one
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-18T17:46:01.021299+00:00
-- url     : https://prove2.me/theorems/badac01f-3d23-49b6-a53c-10aef5c28055
-- title:
--   Every coefficient of a power of the positive logarithmic majorant is at most one
-- statement:
--   For all natural q and k, the coefficient magnitude of the q-th power of the majorant is at most 1. For q≤k its coefficient is q! times the unsigned Stirling number of the first kind divided by k!, bounded by 1 by counting permutations with q cycles; outside that range it is zero, with the q=k=0 coefficient equal to 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_one (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤ 1 := by sorry
