-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_sum_conj_eq_sum_subgroupOf
-- name    : GroundTheory.Global.Artin.sum_conj_eq_sum_subgroupOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:50.32975+00:00
-- url     : https://prove2.me/theorems/c6b219ea-3be3-5474-9b71-4d82ca1be45f
-- title:
--   Artin: sum conj eq sum subgroup Of
-- statement:
--   The Artin construction uses the sum conj eq sum subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L101-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L101-L137

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

theorem GroundTheory.Global.Artin.sum_conj_eq_sum_subgroupOf (H I : Subgroup G) [Fintype I] (x : G)
    [Fintype ((MulAut.conj x • I : Subgroup G).subgroupOf H)] (F : G → ℂ)
    (hF : ∀ g ∉ H, F g = 0) :
    ∑ i : I, F (x * i * x⁻¹) =
      ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, F ((j : H) : G) := by sorry
