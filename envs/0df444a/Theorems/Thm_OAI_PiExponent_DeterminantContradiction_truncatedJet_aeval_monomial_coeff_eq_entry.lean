-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedJet_aeval_monomial_coeff_eq_entry
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedJet_aeval_monomial_coeff_eq_entry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:36:10.565964+00:00
-- url     : https://prove2.me/theorems/a6c78c9f-8901-4d92-8901-915ae578e252
-- title:
--   The aeval monomial coefficient equals its interpolation entry
-- statement:
--   For any dimension, truncation orders, substitution scale, monomial exponent vector, and coefficient index, the coefficient of the substituted monomial equals the corresponding iterated coefficient defining the interpolation matrix entry.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedJet_aeval_monomial_coeff_eq_entry
    {m : Nat} (r : Fin m → Complex) (T : Fin m → Nat)
    (j : Nat) (c b : Fin (m + 1) → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0)
            (InterpolationMatrix.truncatedLog (T i))))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector c) 1)).coeff
      (InterpolationMatrix.exponentVector b) =
      InterpolationMatrix.entry r
        (fun i => InterpolationMatrix.truncatedLog (T i)) j (b 0)
        (fun i => b i.succ) (c 0) (fun i => c i.succ) := by sorry
