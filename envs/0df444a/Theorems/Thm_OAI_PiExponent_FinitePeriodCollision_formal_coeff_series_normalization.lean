-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_formal_coeff_series_normalization
-- name    : OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:24:48.124787+00:00
-- url     : https://prove2.me/theorems/16ce493f-f06e-4210-b132-337faa70b799
-- title:
--   Combine the formal logarithm powers
-- statement:
--   Replace the finite product of powers of the same formal series by one power whose exponent is the sum. This removes the multi-index algebra from the parent. The identity follows from the finite-product power law in the commutative power-series ring; it preserves the exact natural subtraction, including zero exponents when A exceeds a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (∑ i, (a i - A i))) := by sorry
