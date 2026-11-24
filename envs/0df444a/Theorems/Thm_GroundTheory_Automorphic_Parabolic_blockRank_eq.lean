-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_eq
-- name    : GroundTheory.Automorphic.Parabolic.blockRank_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:24:06.215814+00:00
-- url     : https://prove2.me/theorems/97826feb-9010-4965-bf7f-2deb0583a5d4
-- title:
--   Parabolic: block Rank eq
-- statement:
--   The Parabolic construction uses the block Rank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L219-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L219-L220

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

theorem GroundTheory.Automorphic.Parabolic.blockRank_eq {i j : Fin n} (h : β i = β j) : blockRank β i = blockRank β j := by sorry
