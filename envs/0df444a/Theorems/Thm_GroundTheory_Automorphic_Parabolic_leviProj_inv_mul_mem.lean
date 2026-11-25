-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_inv_mul_mem
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_inv_mul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:26.4438+00:00
-- url     : https://prove2.me/theorems/beb89969-fbd6-46ee-8cbb-031c2ace56c8
-- title:
--   Parabolic: levi Proj inv mul mem
-- statement:
--   The Parabolic construction uses the levi Proj inv mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L184-L186

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

theorem GroundTheory.Automorphic.Parabolic.leviProj_inv_mul_mem (p : blockUpper F n β) :
    ((leviIncl (leviProj F n β p))⁻¹ * p : blockUpper F n β).1 ∈ unipotentRadical F n β := by sorry
