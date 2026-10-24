-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_unscaled
-- name    : OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_unscaled
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:29:53.791672+00:00
-- url     : https://prove2.me/theorems/83982017-4932-4a72-8c4b-2e4b0238f027
-- title:
--   Unscaled jet monomial coefficient bridge
-- statement:
--   For arbitrary centers and truncation orders, substituting the specified truncated jets into the monomial with exponent vector `Fin.cases h a` and extracting the `Fin.cases s b` coefficient agrees with first extracting the `b` coefficient of the corresponding monomial image and then extracting polynomial degree `s`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_unscaled
    (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by sorry
