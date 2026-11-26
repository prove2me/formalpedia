-- Prove2me | Theorems.Thm_OrderExpander_IsSegment_U_of_Good
-- name    : OrderExpander.IsSegment_U_of_Good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:30.141876+00:00
-- url     : https://prove2.me/theorems/026e5335-289f-5e8c-a5a6-a00019edc8e9
-- title:
--   Order Expander: Is Segment U of Good
-- statement:
--   Every good chain is a segment of `U`.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L211-L219
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L211-L219

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]

theorem OrderExpander.IsSegment_U_of_Good {D : Set α} (goodD : Good D) : D ⊑ U := by sorry
