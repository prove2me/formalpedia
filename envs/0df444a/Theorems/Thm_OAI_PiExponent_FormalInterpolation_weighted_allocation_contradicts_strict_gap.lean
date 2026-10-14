-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_allocation_contradicts_strict_gap
-- name    : OAI.PiExponent.FormalInterpolation.weighted_allocation_contradicts_strict_gap
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:19:23.219987+00:00
-- url     : https://prove2.me/theorems/0245ae06-64b9-4b63-ae5a-92186b82d694
-- title:
--   A bounded coefficient allocation contradicts a strict weight gap
-- statement:
--   Under the factor coefficient weight bounds and the strict target weight gap, no coordinatewise bounded allocation summing to the target can have all its factor coefficients nonzero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_allocation_contradicts_strict_gap
    {m n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hcoeff : ∀ i b, b ≤ a →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector b) (F i) ≠ 0 →
        R i ≤ ∑ j, v j * (b j : Real))
    (hweight : ∑ j, v j * (a j : Real) < ∑ i, R i)
    (b : Fin n → Fin (m + 1) → Nat)
    (hbound : ∀ i, b i ≤ a)
    (hsum : ∀ j, (∑ i, b i j) = a j)
    (hnz : ∀ i, MvPolynomial.coeff (InterpolationMatrix.exponentVector (b i)) (F i) ≠ 0) :
    False := by sorry
