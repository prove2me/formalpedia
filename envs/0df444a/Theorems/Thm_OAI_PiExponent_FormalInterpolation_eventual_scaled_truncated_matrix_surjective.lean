-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_scaled_truncated_matrix_surjective
-- name    : OAI.PiExponent.FormalInterpolation.eventual_scaled_truncated_matrix_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T04:52:42.464163+00:00
-- url     : https://prove2.me/theorems/2d4787ab-8c62-467f-9559-5309c6649c87
-- title:
--   Eventual surjectivity of the scaled truncated interpolation matrix
-- statement:
--   Under the scale and row-weight hypotheses, there is a threshold after which the truncated logarithmic interpolation matrix is surjective at each scale nR.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_scaled_truncated_matrix_surjective
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
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))
          ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          T).mulVecLin := by sorry
