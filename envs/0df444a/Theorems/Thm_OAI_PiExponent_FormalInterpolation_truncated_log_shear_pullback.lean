-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_shear_pullback
-- name    : OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:34:11.350486+00:00
-- url     : https://prove2.me/theorems/cfc50b7e-b590-4101-be34-bca24f0568ca
-- title:
--   Undo the truncated logarithmic substitution by a polynomial shear
-- statement:
--   For every truncation profile and polynomial Q, one polynomial P cancels the truncated-log correction simultaneously at every center c, leaving Q translated by the point whose first coordinate is zero and remaining coordinates are c. This isolates the change-of-variables algebra from the parent. Its direct proof substitutes the first variable minus one and each later variable minus its truncated-log polynomial evaluated at the first variable minus one.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback
    {m : Nat} (T : Fin m → Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex, ∀ c : Fin m → Complex,
      truncatedPolynomialJet c T P =
      MvPolynomial.aeval
        (fun i : Fin (m + 1) =>
          MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i) Q := by sorry
