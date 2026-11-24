-- Prove2me | Theorems.Thm_GlobalTheory_isLeftCoaction_iff_isCoaction_comm
-- name    : GlobalTheory.isLeftCoaction_iff_isCoaction_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:24.593579+00:00
-- url     : https://prove2.me/theorems/8b3d74fa-6c1c-4f24-bbce-491c71fbf071
-- title:
--   Global Theory: is Left Coaction iff is Coaction comm
-- statement:
--   The Global Theory construction uses the is Left Coaction iff is Coaction comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L52-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L52-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

theorem GlobalTheory.isLeftCoaction_iff_isCoaction_comm [IsCocomm R C] (ρ : M →ₗ[R] C ⊗[R] M) :
    IsLeftCoaction ρ ↔ IsCoaction ((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ) := by sorry
