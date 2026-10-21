-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_product_coordinate_factors
-- name    : OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:27:00.790226+00:00
-- url     : https://prove2.me/theorems/3740ed69-880a-441f-bfdb-db58a3a4c8a5
-- title:
--   Coefficient extraction across independent coordinates
-- statement:
--   The coefficient at a multi-index of a product of coordinatewise polynomials is the product of the corresponding single-coordinate coefficients. Each factor is supported only on monomials in its own coordinate, so no other allocation of exponents contributes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      ∏ i, ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (Finsupp.single i (A i)) := by sorry
