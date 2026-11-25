-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_normal_of_le_of_zpowers_eq_top
-- name    : GroundTheory.Global.Artin.normal_of_le_of_zpowers_eq_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:03.225527+00:00
-- url     : https://prove2.me/theorems/cf7dafc7-bed2-4341-939c-20a4afcd329f
-- title:
--   Artin: normal of le of zpowers eq top
-- statement:
--   The Artin construction uses the normal of le of zpowers eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L31-L39

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}

theorem GroundTheory.Global.Artin.normal_of_le_of_zpowers_eq_top (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) : K.Normal := by sorry
