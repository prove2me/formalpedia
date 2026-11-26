-- Prove2me | Theorems.Thm_OrderSelector_wellOrdered_of_good
-- name    : OrderSelector.wellOrdered_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:50.030263+00:00
-- url     : https://prove2.me/theorems/3ac6befa-17ec-502d-aa1d-a897bd5c2276
-- title:
--   Order Selector: well Ordered of good
-- statement:
--   Every good chain for the successor function `C ↦ C ∪ {f C}` is well-ordered by the strict
--   order of the poset, in the sense that every nonempty subset of the chain has a least
--   element. This is Proposition `prop:good-well-ordered` of the paper, restricted to the
--   `OrderSelector` setting.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L306-L364
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L306-L364

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

theorem OrderSelector.wellOrdered_of_good {C : Set α} (hC : Good C) (X : Set α) (hXC : X ⊆ C)
    (hne : X.Nonempty) : ∃ m ∈ X, ∀ y ∈ X, m ≤ y := by sorry
