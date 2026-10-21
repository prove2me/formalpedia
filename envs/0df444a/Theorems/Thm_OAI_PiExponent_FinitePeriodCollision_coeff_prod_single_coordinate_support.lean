-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_prod_single_coordinate_support
-- name    : OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:31:10.55363+00:00
-- url     : https://prove2.me/theorems/0ab53423-e7f3-45e3-8355-2f1454996875
-- title:
--   Product coefficient for single-coordinate supports
-- statement:
--   For a finite family of multivariate polynomials where each factor is supported on its own variable, the product coefficient at exponent vector `A` equals the product of each factor's coefficient at that variable's exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Mathlib.Algebra.MvPolynomial.Basic
open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (f : σ → MvPolynomial σ R) (A : σ → ℕ)
    (hsupport : ∀ (i : σ) (s : σ →₀ ℕ), (f i).coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    (∏ i, f i).coeff (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, (f i).coeff (Finsupp.single i (A i)) := by sorry
