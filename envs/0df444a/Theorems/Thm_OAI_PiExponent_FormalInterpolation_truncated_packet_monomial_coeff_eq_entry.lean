-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_monomial_coeff_eq_entry
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_monomial_coeff_eq_entry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:56:01.280262+00:00
-- url     : https://prove2.me/theorems/9779ab55-5816-40c0-8cea-38f6b5e5f6e6
-- title:
--   A column monomial packet coefficient is its matrix entry
-- statement:
--   For a fixed row and column, the coefficient extracted from the substituted column monomial equals its scalar coefficient times the corresponding truncated logarithm matrix entry.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_monomial_coeff_eq_entry
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (rho : InterpolationMatrix.Row K v0 theta w H)
    (c : InterpolationMatrix.Column w0 w H) (z : Complex) :
    (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) z)).coeff
        (InterpolationMatrix.exponentVector rho.2.val) =
      z * InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
        (c.1 0) (fun i => c.1 i.succ) := by sorry
