-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_packet_representative_from_matrix_surjectivity
-- name    : OAI.PiExponent.FormalInterpolation.bounded_packet_representative_from_matrix_surjectivity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:22:10.287222+00:00
-- url     : https://prove2.me/theorems/69794f7e-672b-4c5a-a7ff-d05eb2b683cf
-- title:
--   Bounded packet representatives from matrix surjectivity
-- statement:
--   If the truncated logarithm matrix is surjective at the weight bound nR, every polynomial has a weighted representative at that bound with the same truncated packet.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_packet_representative_from_matrix_surjectivity
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
    (n : Nat) (P : MvPolynomial (Fin (d.m + 1)) Complex)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin) :
    ∃ Q : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val := by sorry
