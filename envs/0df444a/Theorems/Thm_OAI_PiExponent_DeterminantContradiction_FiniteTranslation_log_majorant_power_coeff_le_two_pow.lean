-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_le_two_pow
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_two_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:06:53.270868+00:00
-- url     : https://prove2.me/theorems/62d48af9-6b42-4390-835e-f62df6adddf6
-- title:
--   Degree-exponential coefficient bound for powers of the positive logarithmic majorant
-- statement:
--   For every natural exponent q and degree k, the coefficient magnitude of (sum over n≥1 of X^n/n)^q is at most 2^k. Expand over ordered positive compositions of k, bound each reciprocal-product summand by one, and count compositions using subsets of the k−1 possible cuts. Handle zero powers and degree zero separately.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_two_pow
    (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
      (2 : ℝ) ^ k := by sorry
