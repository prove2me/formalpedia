-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_inverse_shear_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.truncated_log_inverse_shear_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:11:36.09271+00:00
-- url     : https://prove2.me/theorems/e6bb803a-b12d-470f-aa40-556cab931d1f
-- title:
--   Coordinate images under the inverse truncated-log shear
-- statement:
--   For each coordinate, evaluating its inverse-shear polynomial through the truncated polynomial jet gives the corresponding translation coordinate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_log_inverse_shear_coordinate
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (i : Fin (m + 1)) :
    MvPolynomial.aeval
      (fun k : Fin (m + 1) =>
        Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
          (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
            Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))
              (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) k)
      (Fin.cases
        (MvPolynomial.X (0 : Fin (m + 1)) -
          (1 : MvPolynomial (Fin (m + 1)) Complex))
        (fun j => MvPolynomial.X j.succ -
          Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) -
              (1 : MvPolynomial (Fin (m + 1)) Complex))
            (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) i) =
    MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i := by sorry
