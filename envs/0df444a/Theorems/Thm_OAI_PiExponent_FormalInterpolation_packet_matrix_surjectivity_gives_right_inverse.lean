-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_matrix_surjectivity_gives_right_inverse
-- name    : OAI.PiExponent.FormalInterpolation.packet_matrix_surjectivity_gives_right_inverse
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T04:52:58.282142+00:00
-- url     : https://prove2.me/theorems/e7edc581-1479-4c85-b074-573e9e37b80a
-- title:
--   Lift matrix surjectivity to a packet-map right inverse
-- statement:
--   At a fixed scale, surjectivity of the truncated interpolation matrix and the row-weight bound yield a right inverse for the packet map into weighted polynomials.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.packet_matrix_surjectivity_gives_right_inverse
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin) :
    ∃ F : (Row d H → Complex) →
        WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      ∀ y : Row d H → Complex, packetMap d H (F y) = y := by sorry
