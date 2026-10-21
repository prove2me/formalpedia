-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_prod_single_coordinate_monomial_sum
-- name    : OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:23:52.069171+00:00
-- url     : https://prove2.me/theorems/ef3deb73-9470-49c7-8887-3e217b1df693
-- title:
--   Coefficient of a product of finite single-coordinate monomial sums
-- statement:
--   The coefficient of a product of finite single-coordinate monomial sums is the product of the requested coefficients, with zero whenever a requested exponent is absent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Mathlib.Algebra.MvPolynomial.Basic
open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (S : σ → Finset ℕ) (c : σ → ℕ → R) (A : σ → ℕ) :
    (∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n) (c i n)).coeff
        (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, if A i ∈ S i then c i (A i) else 0 := by sorry
