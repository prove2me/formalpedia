-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_conj_mem_of_le
-- name    : GroundTheory.Global.Artin.zpow_inv_mul_conj_mem_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:03.874164+00:00
-- url     : https://prove2.me/theorems/ffabcfe0-841b-587c-a179-14f68b40fa7c
-- title:
--   Artin: zpow inv mul conj mem of le
-- statement:
--   The Artin construction uses the zpow inv mul conj mem of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L76-L80

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

theorem GroundTheory.Global.Artin.zpow_inv_mul_conj_mem_of_le [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (m : ℤ) : (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) ∈ I := by sorry
