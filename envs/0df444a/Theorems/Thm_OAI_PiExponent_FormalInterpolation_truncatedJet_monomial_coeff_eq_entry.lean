-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry
-- name    : OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:26:00.657286+00:00
-- url     : https://prove2.me/theorems/d443755e-864d-47ec-8649-e0aedd0549f6
-- title:
--   Monomial jet coefficients equal interpolation matrix entries
-- statement:
--   For arbitrary centers, polynomial translates, and natural row and column exponents, evaluating the column monomial at the translated variables and extracting the combined exponent vector gives the corresponding nested polynomial and multivariate coefficient in the interpolation matrix entry. Zero exponents and arbitrary indices are allowed; no positivity assumptions are needed.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry
    {m : ℕ} (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (j s h : ℕ) (b a : Fin m → ℕ) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : ℂ) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : ℂ))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by sorry
