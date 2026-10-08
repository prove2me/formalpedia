-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
-- name    : OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:13:32.294087+00:00
-- url     : https://prove2.me/theorems/ba764e54-2528-47dc-b194-c219738df2d4
-- title:
--   Explicit coefficient vector realizes each packet
-- statement:
--   For a weighted polynomial and truncation orders satisfying the cutoff bound, the interpolation matrix realizes every packet when its column indexed by a monomial exponent is assigned the coefficient of that monomial in the polynomial. The key point is that the cutoff condition makes the truncated logarithmic substitutions agree with the formal packet coefficients on every row.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean (coefficient identity for the truncated logarithmic interpolation matrix)

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
    {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)) :
    ∀ ρ : Row d (H : ℝ),
      (actualMatrix d (H : ℝ)).mulVecLin
        (fun c : Column d (H : ℝ) => P.val.coeff (InterpolationMatrix.exponentVector c.1)) ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by sorry
