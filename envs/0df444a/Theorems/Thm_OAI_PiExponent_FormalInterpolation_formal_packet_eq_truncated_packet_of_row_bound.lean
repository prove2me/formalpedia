-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formal_packet_eq_truncated_packet_of_row_bound
-- name    : OAI.PiExponent.FormalInterpolation.formal_packet_eq_truncated_packet_of_row_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T07:11:17.628153+00:00
-- url     : https://prove2.me/theorems/cf93c7d8-737f-45f9-99ff-280408627585
-- title:
--   Identify formal packets with truncated packets under row bounds
-- statement:
--   For every weighted polynomial, its formal packet map equals the truncated polynomial packet when the row weights satisfy the stated truncation bounds. This transfers the coefficient calculation from the formal power-series jet to the finite truncated-log jet.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.formal_packet_eq_truncated_packet_of_row_bound
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    packetMap d H P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val := by sorry
