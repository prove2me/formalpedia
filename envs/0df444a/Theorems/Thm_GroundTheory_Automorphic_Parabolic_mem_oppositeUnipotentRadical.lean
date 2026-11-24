-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_oppositeUnipotentRadical
-- name    : GroundTheory.Automorphic.Parabolic.mem_oppositeUnipotentRadical
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:37.022809+00:00
-- url     : https://prove2.me/theorems/6a3c0bc8-d597-4064-9450-0a5a82827384
-- title:
--   Parabolic: mem opposite Unipotent Radical
-- statement:
--   The Parabolic construction uses the mem opposite Unipotent Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L154-L160

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.mem_oppositeUnipotentRadical {g : GL (Fin n) F} :
    g ∈ oppositeUnipotentRadical F n β ↔ (∀ i j, β i < β j → g i j = 0) ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by sorry
