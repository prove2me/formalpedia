-- Prove2me | Theorems.Thm_GlobalTheory_T_rational_matrix_identity_transfer_to_complex_map
-- name    : GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:48.601934+00:00
-- url     : https://prove2.me/theorems/cc9da80d-bb79-4758-94ae-bbd3c8918768
-- title:
--   T: rational matrix identity transfer to complex map
-- statement:
--   The T construction uses the rational matrix identity transfer to complex map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalMatrixIdentityTransferToComplexMapStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalMatrixIdentityTransferToComplexMapStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalMatrixIdentityTransferToComplexMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalMatrixIdentityTransferToComplexMapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq) →
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by sorry
