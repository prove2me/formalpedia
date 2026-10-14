-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coeff_vanishes_for_product_on_weighted_simplex
-- name    : OAI.PiExponent.FormalInterpolation.coeff_vanishes_for_product_on_weighted_simplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:36:00.766783+00:00
-- url     : https://prove2.me/theorems/313e220a-cfd9-4be8-98f7-596f9a3f0678
-- title:
--   Coefficient vanishing for products on weighted simplexes
-- statement:
--   If each polynomial has zero coefficients at every exponent in a strict weighted simplex of its assigned positive height, then their product has zero coefficients at every exponent in the strict weighted simplex whose height is the sum of those heights.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coeff_vanishes_for_product_on_weighted_simplex
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (hR : ∀ i, 0 < R i)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hF : ∀ i a, a ∈ PiExponent.strictWeightedSimplex v (R i) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (F i) = 0) :
    ∀ a, a ∈ PiExponent.strictWeightedSimplex v (∑ i, R i) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) = 0 := by sorry
