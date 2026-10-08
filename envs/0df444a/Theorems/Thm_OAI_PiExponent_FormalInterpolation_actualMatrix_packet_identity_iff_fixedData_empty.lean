-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_packet_identity_iff_fixedData_empty
-- name    : OAI.PiExponent.FormalInterpolation.actualMatrix_packet_identity_iff_fixedData_empty
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-08T06:16:40.105053+00:00
-- url     : https://prove2.me/theorems/1b1e7f6e-c91e-4f63-8845-2a5d6d3e97b4
-- title:
--   The full packet coefficient identity is equivalent to emptiness of FixedData
-- statement:
--   Let $E$ be the universal coefficient identity asserted in `OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients`: for every exponent, admissible fixed data, height, weighted polynomial, and row, the truncated interpolation matrix applied to the polynomial coefficients agrees with its full formal logarithmic packet, under the stated cutoff bound. Then
--
--   $$E \quad\Longleftrightarrow\quad \forall\nu\in\mathbb R,\;\operatorname{FixedData}(\nu)=\varnothing.$$
--
--   This is an obstruction theorem for that precise identity. The implication to emptiness uses positive weights and the full FixedData assumptions; it does not rely on the zero-weight counterexample to the earlier generalized child. The reverse implication is vacuous. The result asserts neither existence nor nonexistence of FixedData, and therefore does not by itself prove or disprove the coefficient identity.
-- source:
--   Original obstruction derived from the target https://prove2.me/theorems/ba764e54-2528-47dc-b194-c219738df2d4 and its definitions. Compare openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean, theorem truncatedLogMatrix_mulVec_eq_coeff, which concerns the truncated jet, not the full jet. https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.actualMatrix_packet_identity_iff_fixedData_empty :
    (∀ {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)), ∀ ρ : Row d (H : ℝ),
      (actualMatrix d (H : ℝ)).mulVecLin
        (fun c : Column d (H : ℝ) => P.val.coeff (InterpolationMatrix.exponentVector c.1)) ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ) ↔
    (∀ nu : ℝ, IsEmpty (FixedData nu)) := by sorry
