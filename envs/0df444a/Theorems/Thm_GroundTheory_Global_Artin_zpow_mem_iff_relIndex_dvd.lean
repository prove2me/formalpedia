-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpow_mem_iff_relIndex_dvd
-- name    : GroundTheory.Global.Artin.zpow_mem_iff_relIndex_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:13.899144+00:00
-- url     : https://prove2.me/theorems/4c1fee6d-09c7-5df0-aa7d-753cd5ed2238
-- title:
--   Artin: zpow mem iff rel Index dvd
-- statement:
--   The Artin construction uses the zpow mem iff rel Index dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L93-L99

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
variable {G : Type*} [Group G]
variable {H D I : Subgroup G}

theorem GroundTheory.Global.Artin.zpow_mem_iff_relIndex_dvd [Finite G] [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {K : Subgroup G}
    (hIK : I ≤ K) (m : ℤ) : φ ^ m ∈ K ↔ (K.relIndex D : ℤ) ∣ m := by sorry
