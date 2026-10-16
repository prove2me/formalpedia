-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_column_sum_linear
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_column_sum_linear
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:55:43.558968+00:00
-- url     : https://prove2.me/theorems/e4db1ee5-6015-48fa-97c1-17282919c1af
-- title:
--   Linearity of the truncated packet on a column monomial sum
-- statement:
--   At each row, the truncated packet of the finite sum of column monomials equals the sum of the packets of those monomials.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_column_sum_linear
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    truncatedPolynomialPacket K v0 theta w H r T
        (∑ c : InterpolationMatrix.Column w0 w H,
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) rho =
      ∑ c : InterpolationMatrix.Column w0 w H,
        truncatedPolynomialPacket K v0 theta w H r T
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) rho := by sorry
