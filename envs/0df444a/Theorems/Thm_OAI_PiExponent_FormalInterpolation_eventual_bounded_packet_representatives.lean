-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_packet_representatives
-- name    : OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T09:33:32.884296+00:00
-- url     : https://prove2.me/theorems/4f1b4a74-f70d-44b6-a32d-268bf1eb0ef5
-- title:
--   Eventual bounded representatives with equal truncated packets
-- statement:
--   Under the target's scaling and truncation hypotheses, every polynomial has, for all sufficiently large n, a representative with weighted support at most nR and the same truncated logarithmic packet. This isolates the eventual bounded interpolation step from the later ideal-power argument. A direct proof must establish the eventual interpolation/rank result with the stated weight cutoff; the cyclic matrix-surjectivity dependency cannot be used.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
      ∃ Q : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val := by sorry
