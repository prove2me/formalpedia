-- Prove2me | Theorems.Thm_GlobalTheory_isCoaction_of_isGroupLikeElem
-- name    : GlobalTheory.isCoaction_of_isGroupLikeElem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:58.025439+00:00
-- url     : https://prove2.me/theorems/aaa8ff9b-9e8b-5cb4-9fac-9e59c2524331
-- title:
--   Global Theory: is Coaction of is Group Like Elem
-- statement:
--   The Global Theory construction uses the is Coaction of is Group Like Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L38-L41

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
variable (M)

theorem GlobalTheory.isCoaction_of_isGroupLikeElem {g : C} (hg : IsGroupLikeElem R g) :
    IsCoaction ((TensorProduct.mk R M C).flip g) := by sorry
