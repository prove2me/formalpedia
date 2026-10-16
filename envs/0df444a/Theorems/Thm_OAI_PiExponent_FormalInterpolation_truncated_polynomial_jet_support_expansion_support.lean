-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion_support
-- name    : OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:58:44.329127+00:00
-- url     : https://prove2.me/theorems/9097e00a-d77f-403e-bfc2-4ad94e189e26
-- title:
--   Expand a jet coefficient over polynomial support
-- statement:
--   The coefficient of the jet of any polynomial is the support sum of its coefficients multiplied by the corresponding coefficient of the jet of each support monomial.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_support
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T P).coeff
        (InterpolationMatrix.exponentVector a) =
      ∑ e ∈ P.support,
        P.coeff e *
          (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
            (MvPolynomial.monomial e (1 : Complex))).coeff
            (InterpolationMatrix.exponentVector a) := by sorry
