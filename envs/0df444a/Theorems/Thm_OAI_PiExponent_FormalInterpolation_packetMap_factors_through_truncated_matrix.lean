-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packetMap_factors_through_truncated_matrix
-- name    : OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T07:06:06.208896+00:00
-- url     : https://prove2.me/theorems/b932ea69-a551-4daf-9a77-ac932e0fe442
-- title:
--   Represent truncated matrix images by formal packets
-- statement:
--   For every coefficient vector, construct a weighted polynomial whose formal packet map agrees with the truncated interpolation matrix applied to that vector, using the row-weight bound.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0) :
    ∀ x : InterpolationMatrix.Column d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H → Complex,
      ∃ P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H,
        packetMap d H P =
          (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d)) T).mulVecLin x := by sorry
