-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap
-- name    : OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T19:49:27.535989+00:00
-- url     : https://prove2.me/theorems/7769fb08-f620-4843-aa1f-9ade31c94fa5
-- title:
--   Realize formal packets by actual matrix columns
-- statement:
--   For an admissible determinant family and a weighted polynomial P, the finite coefficient vector of P in the weighted monomial basis can be chosen so that applying the actual matrix to that vector reproduces, row by row, the formal logarithmic packet map of P. This is the coefficient-transfer step from formal jets to the concrete truncated matrix.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean and Approximation/AdmissibleMatrixInterpolation.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap
    {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) (H : ℝ)) :
    ∃ x : Column d (H : ℝ) → ℂ,
      ∀ ρ : Row d (H : ℝ),
        (actualMatrix d (H : ℝ)).mulVecLin x ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by sorry
