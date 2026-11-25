-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_selfAdjoint_endo_relating_hermitian_forms
-- name    : GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:49.500632+00:00
-- url     : https://prove2.me/theorems/470db812-d453-5bbb-b550-3e332e49109b
-- title:
--   T: exists self Adjoint endo relating hermitian forms
-- statement:
--   The T construction uses the exists self Adjoint endo relating hermitian forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianFormsStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianFormsStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfAdjointEndoRelatingHermitianForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfAdjointEndoRelatingHermitianFormsStatement
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

theorem GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by sorry
