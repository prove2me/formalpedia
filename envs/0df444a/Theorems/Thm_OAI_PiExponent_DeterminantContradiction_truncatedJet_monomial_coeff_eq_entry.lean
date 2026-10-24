-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedJet_monomial_coeff_eq_entry
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedJet_monomial_coeff_eq_entry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:28:27.159212+00:00
-- url     : https://prove2.me/theorems/fea998e3-41f5-4c26-b702-fe0f53a319b7
-- title:
--   Truncated jet monomial coefficient equals the interpolation entry
-- statement:
--   For any interpolation dimension, truncation orders, indices, exponents, and scalar, the coefficient of the truncated jet image of a scalar multiple of a selected monomial equals that scalar times the corresponding interpolation matrix entry.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedJet_monomial_coeff_eq_entry
    {m : Nat} (r : Fin m → Complex) (T : Fin m → Nat)
    (j s h : Nat) (a b : Fin m → Nat) (z : Complex) :
    (OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet
      (fun i => (j : Complex) * r i) T
      (MvPolynomial.C z *
        MvPolynomial.monomial
          (OAI.PiExponent.InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (OAI.PiExponent.InterpolationMatrix.exponentVector (Fin.cases s b)) =
      z * OAI.PiExponent.InterpolationMatrix.entry r
        (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) j s b h a := by sorry
