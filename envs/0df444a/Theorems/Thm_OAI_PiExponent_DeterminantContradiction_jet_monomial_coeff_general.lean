-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_general
-- name    : OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:54:08.134105+00:00
-- url     : https://prove2.me/theorems/b6a24bed-9717-4515-b771-6617696412e7
-- title:
--   General coefficient bridge for substituted monomials
-- statement:
--   For arbitrary centers and polynomial shifts, extracting the coefficient after substituting into a monomial agrees with extracting the corresponding polynomial coefficient from the explicit product representation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_general
    (m : Nat) (c : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (h : Nat) (a : Fin m → Nat) (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by sorry
