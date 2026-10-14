-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_surjective_of_matrix_surjective
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_surjective_of_matrix_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:26:56.193466+00:00
-- url     : https://prove2.me/theorems/c06c2681-e2b6-4597-945d-e973866e301d
-- title:
--   Matrix surjectivity gives bounded truncated packet representatives
-- statement:
--   If the truncated logarithm matrix is surjective, every row function is the truncated packet of a weighted polynomial at the specified bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_surjective_of_matrix_surjective
    (nu : Real) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (n : Nat)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin)
    (y : InterpolationMatrix.Row d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) → Complex) :
    ∃ Q : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val = y := by sorry
