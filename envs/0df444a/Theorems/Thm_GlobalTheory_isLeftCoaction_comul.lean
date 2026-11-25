-- Prove2me | Theorems.Thm_GlobalTheory_isLeftCoaction_comul
-- name    : GlobalTheory.isLeftCoaction_comul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:20.736272+00:00
-- url     : https://prove2.me/theorems/0d30a6ee-9e91-5168-bc23-f37a1dc1597f
-- title:
--   Global Theory: is Left Coaction comul
-- statement:
--   The Global Theory construction uses the is Left Coaction comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L32-L34

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
variable (R C)

theorem GlobalTheory.isLeftCoaction_comul : IsLeftCoaction (comul : C →ₗ[R] C ⊗[R] C) := by sorry
