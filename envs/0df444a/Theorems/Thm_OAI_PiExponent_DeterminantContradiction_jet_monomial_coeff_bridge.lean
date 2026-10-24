-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_bridge
-- name    : OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_bridge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:10:22.8592+00:00
-- url     : https://prove2.me/theorems/ee67217d-a179-4880-8d71-0520ae219156
-- title:
--   Jet monomial coefficients agree with nested polynomial coefficients
-- statement:
--   For arbitrary complex centers and truncation orders, the coefficient of a scalar multiple of a monomial after the truncated-jet substitution equals the scalar times the nested coefficient used by the interpolation matrix. This isolates the algebraic coefficient-commutation step from fixed-data and matrix definitions. It applies without positivity assumptions, including zero exponents and zero truncation orders.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_bridge
    (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) (z : Complex) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.C z *
        MvPolynomial.monomial
          (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    z * ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by sorry
