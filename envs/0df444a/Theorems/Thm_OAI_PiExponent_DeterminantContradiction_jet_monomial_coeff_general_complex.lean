-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_general_complex
-- name    : OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_general_complex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:57:46.029524+00:00
-- url     : https://prove2.me/theorems/6adc8794-1f83-4edb-9fa0-f744c59c6f1d
-- title:
--   General monomial coefficient bridge over Complex
-- statement:
--   For arbitrary complex centers and polynomial shifts, extracting a multivariate coefficient after substituting into a monomial equals extracting the corresponding polynomial coefficient from its explicit product representation. The monomial coefficient is explicitly typed over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_general_complex
    (m : Nat) (c : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (h : Nat) (a : Fin m → Nat) (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by sorry
