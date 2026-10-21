-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_formal_coeff_eq_rowTest
-- name    : OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:09:20.272286+00:00
-- url     : https://prove2.me/theorems/2ec46ddb-b84e-4ecb-9f2f-2326337370d4
-- title:
--   Formal shifted-log coefficient equals the analytic Cauchy row test
-- statement:
--   The formal shifted-log power-series coefficient equals the normalized Cauchy coefficient of the corresponding analytic column. This removes the analytic bridge from the parent. A proof route is to apply the Cauchy coefficient formula to the composed analytic function and identify its Taylor series using the logarithm and exponential identities, including cancellation of the natural integer period shift. The exact bridge still requires formalization and verification.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) =
      rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          Complex.log (1 + t))) := by sorry
