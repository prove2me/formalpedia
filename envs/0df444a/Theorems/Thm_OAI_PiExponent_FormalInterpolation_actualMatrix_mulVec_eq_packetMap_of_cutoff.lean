-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap_of_cutoff
-- name    : OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:03:27.790101+00:00
-- url     : https://prove2.me/theorems/39893d2c-f28c-4c1c-963a-9bd2abc99f3c
-- title:
--   Packet realization under truncation cutoffs
-- statement:
--   For fixed admissible interpolation data, a weighted polynomial P is realized by a vector of column coefficients: applying the actual truncated matrix yields the formal packet map at every row, provided each row weight divided by θ is no larger than the corresponding logarithm truncation order times v₀. This isolates the coefficient-transfer identity under the cutoff condition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff
    {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)) :
    ∃ x : Column d (H : ℝ) → ℂ,
      ∀ ρ : Row d (H : ℝ),
        (actualMatrix d (H : ℝ)).mulVecLin x ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by sorry
