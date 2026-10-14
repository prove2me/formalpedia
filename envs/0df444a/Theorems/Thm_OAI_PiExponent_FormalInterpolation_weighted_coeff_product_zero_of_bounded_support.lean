-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coeff_product_zero_of_bounded_support
-- name    : OAI.PiExponent.FormalInterpolation.weighted_coeff_product_zero_of_bounded_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:41:31.386773+00:00
-- url     : https://prove2.me/theorems/f8b34a35-665f-44ed-ac7d-559cbd6039f4
-- title:
--   Weighted support bounds force product coefficient vanishing
-- statement:
--   If every nonzero factor coefficient at an exponent bounded coordinatewise by the target exponent has weighted degree at least that factor’s assigned height, then a target exponent with weighted degree below the sum of the heights has zero coefficient in the product.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_coeff_product_zero_of_bounded_support
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hcoeff : ∀ i b, b ≤ a →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector b) (F i) ≠ 0 →
        R i ≤ ∑ j, v j * (b j : Real))
    (hweight : ∑ j, v j * (a j : Real) < ∑ i, R i) :
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) = 0 := by sorry
