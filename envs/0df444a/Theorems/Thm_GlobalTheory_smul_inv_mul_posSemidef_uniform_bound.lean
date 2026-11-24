-- Prove2me | Theorems.Thm_GlobalTheory_smul_inv_mul_posSemidef_uniform_bound
-- name    : GlobalTheory.smul_inv_mul_posSemidef_uniform_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:05.473933+00:00
-- url     : https://prove2.me/theorems/236ea3ad-cf3e-4a4a-973f-e9394163429c
-- title:
--   Global Theory: smul inv mul pos Semidef uniform bound
-- statement:
--   The Global Theory construction uses the smul inv mul pos Semidef uniform bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L186-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L186-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open WeightedInverseBound

theorem GlobalTheory.smul_inv_mul_posSemidef_uniform_bound : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by sorry
