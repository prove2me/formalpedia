-- Prove2me | Theorems.Thm_OrderExpander_IsChain_U
-- name    : OrderExpander.IsChain_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:37.917037+00:00
-- url     : https://prove2.me/theorems/93f1101e-be42-4cf7-bc4a-22419f7fcb8c
-- title:
--   Order Expander: Is Chain U
-- statement:
--   The union `U` of all good chains is a chain.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L200-L206
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L200-L206

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]

theorem OrderExpander.IsChain_U : IsChain (· ≤ ·) (U  (α := α)) := by sorry
