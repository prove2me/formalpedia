-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_monomial_entry_general
-- name    : OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_monomial_entry_general
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T06:17:23.715989+00:00
-- url     : https://prove2.me/theorems/dc16530b-29af-4a3f-a7ea-aa071483aa2e
-- title:
--   Monomial coefficient identity for arbitrary polynomial jets
-- statement:
--   For any polynomial family G, the coefficient indexed by a in the image of a monomial under the split-variable jet map equals the corresponding interpolation entry. This general support expansion specializes to truncated logarithms.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_monomial_entry_general
    {m : Nat} (j : Nat) (r : Fin m → Complex)
    (G : Fin m → Polynomial Complex)
    (e a : Fin (m + 1) → Nat) :
    (MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
        Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector a) =
      InterpolationMatrix.entry r G j (a 0) (fun i => a i.succ)
        (e 0) (fun i => e i.succ) := by sorry
