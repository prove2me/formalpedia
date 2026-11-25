-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_uniform_bound_smul_inv_add_sum_mul_mulVec
-- name    : GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:39.195616+00:00
-- url     : https://prove2.me/theorems/596f1ecd-718c-4b4a-b0d0-ca9f3621e5c3
-- title:
--   T: exists uniform bound smul inv add sum mul mul Vec
-- statement:
--   The T construction uses the exists uniform bound smul inv add sum mul mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBoundStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBoundStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by sorry
