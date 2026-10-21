-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_single_coordinate_support_as_sum
-- name    : OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:23:33.73393+00:00
-- url     : https://prove2.me/theorems/bade84e7-10c9-4f4f-8fe9-05ee452fde02
-- title:
--   Expansion of a single-coordinate polynomial
-- statement:
--   A polynomial supported only on coordinate i equals the finite sum of its singleton-coordinate monomials, indexed by the coordinate values appearing in its support.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Mathlib.Algebra.MvPolynomial.Basic
open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    p = ∑ n ∈ p.support.image (fun s => s i),
      MvPolynomial.monomial (Finsupp.single i n)
        (p.coeff (Finsupp.single i n)) := by sorry
