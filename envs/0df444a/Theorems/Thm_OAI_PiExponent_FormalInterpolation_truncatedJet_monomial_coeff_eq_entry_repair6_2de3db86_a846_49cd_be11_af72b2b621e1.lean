-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry_repair6_2de3db86_a846_49cd_be11_af72b2b621e1
-- name    : OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair6_2de3db86_a846_49cd_be11_af72b2b621e1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:00:49.070065+00:00
-- url     : https://prove2.me/theorems/90a6006f-45d1-400e-883a-79b6b6dbacac
-- title:
--   General monomial jet coefficient identity
-- statement:
--   For arbitrary complex centers and polynomial translates, evaluating a monomial and extracting the combined exponent vector yields the corresponding nested coefficient in the interpolation matrix entry. This includes zero exponents and zero truncation orders. The helper removes the fixed-data substitution from the parent; its proof expands monomial evaluation and matches the zero-coordinate coefficient with the outer polynomial coefficient, then matches the remaining exponents with the matrix-entry coefficient.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair6_2de3db86_a846_49cd_be11_af72b2b621e1
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
