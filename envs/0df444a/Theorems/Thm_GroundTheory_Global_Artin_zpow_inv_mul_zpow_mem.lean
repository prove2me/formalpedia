-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_zpow_mem
-- name    : GroundTheory.Global.Artin.zpow_inv_mul_zpow_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:11.84534+00:00
-- url     : https://prove2.me/theorems/5415af49-1823-40a9-aaee-a4ac1109dc67
-- title:
--   Artin: zpow inv mul zpow mem
-- statement:
--   The Artin construction uses the zpow inv mul zpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L82-L91

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

theorem GroundTheory.Global.Artin.zpow_inv_mul_zpow_mem [(I.subgroupOf D).Normal] {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a⁻¹ * b ∈ I) (k : ℤ) : (a ^ k)⁻¹ * b ^ k ∈ I := by sorry
