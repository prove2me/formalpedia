-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpow_mem_iff_index_dvd
-- name    : GroundTheory.Global.Artin.zpow_mem_iff_index_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:53.840603+00:00
-- url     : https://prove2.me/theorems/7600d9b5-5f54-46f0-9f5d-df3482c13522
-- title:
--   Artin: zpow mem iff index dvd
-- statement:
--   The Artin construction uses the zpow mem iff index dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L41-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L41-L54

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

theorem GroundTheory.Global.Artin.zpow_mem_iff_index_dvd [Finite Γ] (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) (m : ℤ) : g ^ m ∈ K ↔ (K.index : ℤ) ∣ m := by sorry
