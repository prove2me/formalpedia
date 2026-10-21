-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_single_coordinate_support_mem_iff
-- name    : OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:23:42.597934+00:00
-- url     : https://prove2.me/theorems/ec56064f-6f82-45a6-a8a8-6b1f86b39fbb
-- title:
--   Coordinate support and singleton coefficient
-- statement:
--   For a polynomial supported only on coordinate i, n occurs as that coordinate of a supported exponent exactly when its singleton exponent has nonzero coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Mathlib.Algebra.MvPolynomial.Basic

theorem OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) (n : ℕ) :
    n ∈ p.support.image (fun s => s i) ↔
      p.coeff (Finsupp.single i n) ≠ 0 := by sorry
