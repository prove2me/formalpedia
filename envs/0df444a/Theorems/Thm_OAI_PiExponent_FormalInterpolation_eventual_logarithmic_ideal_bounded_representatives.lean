-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_logarithmic_ideal_bounded_representatives
-- name    : OAI.PiExponent.FormalInterpolation.eventual_logarithmic_ideal_bounded_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:04:44.584697+00:00
-- url     : https://prove2.me/theorems/fb9e0c83-0760-4cab-b330-616ebfba62fc
-- title:
--   Eventual bounded representatives modulo logarithmic center ideal powers
-- statement:
--   Under the prescribed scaling and truncation hypotheses, every polynomial eventually has a representative supported within column weight nR modulo the nth power of the product of logarithmic center ideals.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_logarithmic_ideal_bounded_representatives
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
        P - Q.val ∈ (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i => (j.val : Complex) *
            MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ n := by sorry
