-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_packet_representatives_surjective
-- name    : OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T09:37:20.678348+00:00
-- url     : https://prove2.me/theorems/6db45665-78dc-4c4c-a570-6b2df45b62c2
-- title:
--   Eventual surjectivity of the bounded truncated packet map
-- statement:
--   For all sufficiently large n, the truncated packet map from polynomials with weighted support at most nR onto the full function space on the packet’s row domain is surjective, under the target’s scaling and truncation hypotheses.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives_surjective
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
    ∃ N : Nat, ∀ n : Nat, N ≤ n → Function.Surjective
      (fun Q : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val) := by sorry
