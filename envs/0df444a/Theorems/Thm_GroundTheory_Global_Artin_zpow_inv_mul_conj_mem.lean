-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_conj_mem
-- name    : GroundTheory.Global.Artin.zpow_inv_mul_conj_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:16.053024+00:00
-- url     : https://prove2.me/theorems/451d95dc-2548-406a-9f07-5af79ae24699
-- title:
--   Artin: zpow inv mul conj mem
-- statement:
--   The Artin construction uses the zpow inv mul conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L25-L29

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

theorem GroundTheory.Global.Artin.zpow_inv_mul_conj_mem (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤) (a : Γ) (m : ℤ) :
    (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ N := by sorry
