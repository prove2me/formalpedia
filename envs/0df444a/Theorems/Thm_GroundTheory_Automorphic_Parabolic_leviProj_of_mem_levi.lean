-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_of_mem_levi
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_of_mem_levi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:27.322798+00:00
-- url     : https://prove2.me/theorems/7f61ca98-04f3-4cef-8509-95745b0b986a
-- title:
--   Parabolic: levi Proj of mem levi
-- statement:
--   The Parabolic construction uses the levi Proj of mem levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L116-L118

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

theorem GroundTheory.Automorphic.Parabolic.leviProj_of_mem_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    leviProj F n β ⟨m, levi_le_blockUpper hm⟩ = ⟨m, hm⟩ := by sorry
