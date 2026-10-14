-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_equal_truncated_packets_implies_ideal_power
-- name    : OAI.PiExponent.FormalInterpolation.equal_truncated_packets_implies_ideal_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:22:24.65785+00:00
-- url     : https://prove2.me/theorems/a5c2a89c-ac44-4c8d-9a26-1abbf407c620
-- title:
--   Equal truncated packets imply logarithmic ideal power membership
-- statement:
--   Under the stated truncation and scaling bounds, polynomials with equal truncated packets differ by an element of the nth power of the logarithmic center ideal.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.equal_truncated_packets_implies_ideal_power
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
    (n : Nat) (P Q : MvPolynomial (Fin (d.m + 1)) Complex)
    (hpacket :
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q) :
    P - Q ∈ (logarithmicCentersIdeal
      (fun j : Fin d.K => fun i => (j.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      T e) ^ n := by sorry
