-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry_worker_2de3db86_a846_49cd_be11_af72b2b621e1
-- name    : OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_worker_2de3db86_a846_49cd_be11_af72b2b621e1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:04:15.857693+00:00
-- url     : https://prove2.me/theorems/215c17de-8931-4841-b1f5-a998da238510
-- title:
--   General monomial jet coefficient identity
-- statement:
--   For arbitrary complex centers, polynomial translates, and natural row and column exponents, evaluating the column monomial at the translated variables and extracting the combined exponent vector gives the corresponding nested polynomial coefficient in the interpolation matrix entry. Zero exponents are allowed, including the case where any truncation order is zero. A proof expands evaluation of a monomial and matches the variable-zero coefficient with the outer polynomial coefficient, then matches the other exponents with the matrix-entry coefficient.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_worker_2de3db86_a846_49cd_be11_af72b2b621e1
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j s h : Nat) (b a : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by sorry
