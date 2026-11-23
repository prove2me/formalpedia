-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical_iff_leviProj
-- name    : GroundTheory.Automorphic.Parabolic.mem_unipotentRadical_iff_leviProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:55.923207+00:00
-- url     : https://prove2.me/theorems/a67c2eb6-a9bd-476b-9f4c-c05538eca733
-- title:
--   Parabolic: mem unipotent Radical iff levi Proj
-- statement:
--   The Parabolic construction uses the mem unipotent Radical iff levi Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L165-L172

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

theorem GroundTheory.Automorphic.Parabolic.mem_unipotentRadical_iff_leviProj {p : blockUpper F n β} :
    (p : GL (Fin n) F) ∈ unipotentRadical F n β ↔ leviProj F n β p = 1 := by sorry
