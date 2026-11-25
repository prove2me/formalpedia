-- Prove2me | Theorems.Thm_GlobalTheory_isCoaction_comul
-- name    : GlobalTheory.isCoaction_comul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:12.771794+00:00
-- url     : https://prove2.me/theorems/566ca70b-feb7-46c6-9809-c92b551aae24
-- title:
--   Global Theory: is Coaction comul
-- statement:
--   The Global Theory construction uses the is Coaction comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L26-L28

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

theorem GlobalTheory.isCoaction_comul : IsCoaction (comul : C →ₗ[R] C ⊗[R] C) := by sorry
