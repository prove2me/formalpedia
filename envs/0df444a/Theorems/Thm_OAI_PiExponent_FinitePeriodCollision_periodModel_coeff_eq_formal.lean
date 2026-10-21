-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodModel_coeff_eq_formal
-- name    : OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:08:44.117212+00:00
-- url     : https://prove2.me/theorems/48fb6d1f-e424-4ea5-b2f9-90112cdbf8fa
-- title:
--   Transverse coefficient of the period model
-- statement:
--   The coefficient indexed by A in the period model is the univariate coefficient of the product of the coordinate binomial factors, the period factor, and the shifted-log powers. This removes the multivariate coefficient extraction from the parent. It follows by expanding each coordinate power and using multiplicativity of coefficients across distinct variables; when some A i exceeds a i, both sides vanish due to the binomial factor.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
      ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) := by sorry
