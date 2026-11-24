-- Prove2me | Theorems.Thm_GlobalTheory_eigenTensor_full_left_support
-- name    : GlobalTheory.eigenTensor_full_left_support
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:35.174986+00:00
-- url     : https://prove2.me/theorems/0dc1f81d-c6fc-461f-8ca3-743fea43ff3d
-- title:
--   Global Theory: eigen Tensor full left support
-- statement:
--   The Global Theory construction uses the eigen Tensor full left support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L42-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L42-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct

theorem GlobalTheory.eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by sorry
