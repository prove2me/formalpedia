-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_inv_mul_mul_mem_of_normal
-- name    : GroundTheory.Global.Artin.inv_mul_mul_mem_of_normal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:37.71412+00:00
-- url     : https://prove2.me/theorems/03913e3f-cf7d-5ea8-b3dd-dde4abd10169
-- title:
--   Artin: inv mul mul mem of normal
-- statement:
--   The Artin construction uses the inv mul mul mem of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L71-L74

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

theorem GroundTheory.Global.Artin.inv_mul_mul_mem_of_normal (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] {t i : G}
    (ht : t ∈ D) (hi : i ∈ I) : t⁻¹ * i * t ∈ I := by sorry
