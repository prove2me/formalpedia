-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formal_coeff_eq_truncated_coeff_of_row_bound
-- name    : OAI.PiExponent.FormalInterpolation.formal_coeff_eq_truncated_coeff_of_row_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T07:15:11.281826+00:00
-- url     : https://prove2.me/theorems/e1998472-29aa-41ca-a013-e43582dfb92f
-- title:
--   Formal and truncated jet coefficients agree on bounded rows
-- statement:
--   For generic interpolation data, each row's coefficient in the formal logarithmic jet agrees with the coefficient in the jet formed using the truncated logarithms whenever the row weights satisfy the truncation bounds.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.formal_coeff_eq_truncated_coeff_of_row_bound
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0)
    (P : WeightedPolynomial w0 w H)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
        (formalJet (fun i => (rho.1.val : Complex) * r i) P.val) =
      (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T P.val).coeff
        (InterpolationMatrix.exponentVector rho.2.val) := by sorry
