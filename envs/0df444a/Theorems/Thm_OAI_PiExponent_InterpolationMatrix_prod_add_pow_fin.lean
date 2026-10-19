-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_prod_add_pow_fin
-- name    : OAI.PiExponent.InterpolationMatrix.prod_add_pow_fin
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:49:28.794012+00:00
-- url     : https://prove2.me/theorems/a13a27de-6b23-4b91-95af-062b53ed0fcf
-- title:
--   Dependent finite binomial expansion of a product
-- statement:
--   A product of binomial powers expands over independently bounded exponent choices. Each summand contains the product of binomial coefficients, the complementary powers of the first terms, and the selected powers of the second terms. The bounds include both endpoints and allow zero powers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.prod_add_pow_fin
    {R : Type*} [CommSemiring R] {m : ℕ}
    (x y : Fin m → R) (k : Fin m → ℕ) :
    (∏ i, (x i + y i) ^ k i) =
      ∑ u : (∀ i : Fin m, Fin (k i + 1)),
        ((∏ i, (k i).choose (u i : ℕ) : ℕ) : R) *
          (∏ i, x i ^ (k i - (u i : ℕ))) *
          ∏ i, y i ^ (u i : ℕ) := by sorry
