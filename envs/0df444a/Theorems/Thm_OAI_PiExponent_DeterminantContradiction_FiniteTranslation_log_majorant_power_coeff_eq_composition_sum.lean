-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_eq_composition_sum
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_eq_composition_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:19:44.433972+00:00
-- url     : https://prove2.me/theorems/f27019a3-33a5-4896-b1a7-a445780f7925
-- title:
--   Logarithmic majorant power coefficient as a composition sum
-- statement:
--   The degree-k coefficient of the q-th power of the series with coefficient 0 at degree zero and 1/n at positive degree n is the finite sum, over positive q-tuples summing to k, of the products of their reciprocal entries. The q = 0 and k = 0 cases are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_eq_composition_sum (q k : ℕ) :
    PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹) := by sorry
