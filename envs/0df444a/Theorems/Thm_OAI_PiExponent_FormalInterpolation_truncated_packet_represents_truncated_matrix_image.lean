-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_represents_truncated_matrix_image
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_represents_truncated_matrix_image
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T07:11:45.181252+00:00
-- url     : https://prove2.me/theorems/11833b28-48d2-4f7e-936b-3f2474aa4754
-- title:
--   Represent truncated matrix images by weighted polynomial packets
-- statement:
--   For every coefficient vector, a weighted polynomial can be chosen whose truncated packet is the image of that vector under the truncated interpolation matrix. This is the finite interpolation step of the reduction.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_represents_truncated_matrix_image
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (x : InterpolationMatrix.Column d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val =
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T).mulVecLin x := by sorry
