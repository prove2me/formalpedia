-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_product_C_add_X_pow
-- name    : OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:22:51.094241+00:00
-- url     : https://prove2.me/theorems/06c2e34f-a92d-4085-abd1-8562b2a1ea79
-- title:
--   Coefficient of a product of coordinate binomials
-- statement:
--   The coefficient at exponent vector A of a product of coordinate-wise binomials is the product of the coordinate binomial coefficients times the remaining powers of their constant terms. Coordinates with A i > a i contribute zero on both sides.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        ∏ i, (b i) ^ (a i - A i) := by sorry
