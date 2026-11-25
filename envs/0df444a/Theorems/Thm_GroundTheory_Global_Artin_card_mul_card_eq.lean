-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_card_mul_card_eq
-- name    : GroundTheory.Global.Artin.card_mul_card_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:53:09.683309+00:00
-- url     : https://prove2.me/theorems/9d87f97b-4225-4954-a30d-0e7967c1fbf2
-- title:
--   Artin: card mul card eq
-- statement:
--   The Artin construction uses the card mul card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L157-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L157-L212

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

theorem GroundTheory.Global.Artin.card_mul_card_eq [Finite G] (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] (x : G) :
    Nat.card D * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      frobIndex H D I x * Nat.card I *
        Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by sorry
