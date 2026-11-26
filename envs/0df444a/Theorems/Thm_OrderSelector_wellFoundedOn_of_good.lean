-- Prove2me | Theorems.Thm_OrderSelector_wellFoundedOn_of_good
-- name    : OrderSelector.wellFoundedOn_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:46:10.602799+00:00
-- url     : https://prove2.me/theorems/46edb8b4-34c7-4c81-8309-426c50a9f589
-- title:
--   Order Selector: well Founded On of good
-- statement:
--   The `WellFoundedOn` version of `wellOrdered_of_good`.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L369-L376
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L369-L376

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [OrderSelector α]
open OrderExpander
open OrderSelector

theorem OrderSelector.wellFoundedOn_of_good {C : Set α} (hC : Good C) : C.WellFoundedOn (· < ·) := by sorry
