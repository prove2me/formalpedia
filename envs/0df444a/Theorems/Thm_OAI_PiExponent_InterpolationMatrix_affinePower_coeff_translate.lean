-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_affinePower_coeff_translate
-- name    : OAI.PiExponent.InterpolationMatrix.affinePower_coeff_translate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:49:17.131798+00:00
-- url     : https://prove2.me/theorems/76fa0d9e-733b-4f2f-bcd7-dbc933dcd0de
-- title:
--   Finite coefficient translation for products of affine powers
-- statement:
--   Translating the constants in a product of affine powers expresses each coefficient as a finite binomially weighted sum of the original coefficients. Any finite set containing the coordinate box below the original exponent vector suffices. No restriction on the requested coefficient vector is necessary: binomial factors handle coordinates exceeding the available degrees.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.InterpolationMatrix.affinePower_coeff_translate
    {R : Type*} [CommSemiring R] {m : ℕ}
    (f : R) (z e : Fin m → R) (n b : Fin m → ℕ)
    (S : Finset (Fin m → ℕ))
    (hS : ∀ a : Fin m → ℕ, (∀ i, a i ≤ n i) → a ∈ S) :
    (MvPolynomial.C f *
      ∏ i, (MvPolynomial.C (z i + e i) + MvPolynomial.X i) ^ n i).coeff
        (InterpolationMatrix.exponentVector b) =
      ∑ a : ↥S,
        ((∏ i, (a.1 i).choose (b i) : ℕ) : R) *
          (∏ i, e i ^ (a.1 i - b i)) *
          (MvPolynomial.C f *
            ∏ i, (MvPolynomial.C (z i) + MvPolynomial.X i) ^ n i).coeff
              (InterpolationMatrix.exponentVector a.1) := by sorry
