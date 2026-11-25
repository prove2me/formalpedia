-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_leviIncl
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_leviIncl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:31:02.075833+00:00
-- url     : https://prove2.me/theorems/19467028-d3dc-40d3-a5f1-0bb68b22072c
-- title:
--   Parabolic: levi Proj levi Incl
-- statement:
--   The Parabolic construction uses the levi Proj levi Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L123-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L123-L124

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

theorem GroundTheory.Automorphic.Parabolic.leviProj_leviIncl (m : levi F n β) : leviProj F n β (leviIncl m) = m := by sorry
