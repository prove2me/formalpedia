-- Prove2me | Theorems.Thm_OrderExpander_ssubset_g
-- name    : OrderExpander.ssubset_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:27.41981+00:00
-- url     : https://prove2.me/theorems/ab0c0918-6ccf-532e-9d56-7fdfe29f2e31
-- title:
--   Order Expander: ssubset g
-- statement:
--   The Order Expander construction uses the ssubset g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L173-L174
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L173-L174

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]

theorem OrderExpander.ssubset_g {S C : Set α} (GC : Good C) (prseg : S ⊏ C) : S ⊂ g S := by sorry
