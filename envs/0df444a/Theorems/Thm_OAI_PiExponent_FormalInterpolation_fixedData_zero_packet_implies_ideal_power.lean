-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_zero_packet_implies_ideal_power
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_zero_packet_implies_ideal_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:01:15.451989+00:00
-- url     : https://prove2.me/theorems/83002110-e999-4aa7-a3ed-12473cf5d777
-- title:
--   Fixed-data vanishing packet implies logarithmic ideal power membership
-- statement:
--   For the admissible fixed determinant data, a polynomial whose truncated packet vanishes belongs to the nth power of the corresponding logarithmic center ideal. The hypotheses retain the parent’s positivity, truncation, and scaling bounds.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_zero_packet_implies_ideal_power
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
    (hzero : truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P = 0) :
    P ∈ (logarithmicCentersIdeal
      (fun j : Fin d.K => fun i => (j.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      T e) ^ n := by sorry
