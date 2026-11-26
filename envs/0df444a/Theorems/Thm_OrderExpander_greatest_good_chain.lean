-- Prove2me | Theorems.Thm_OrderExpander_greatest_good_chain
-- name    : OrderExpander.greatest_good_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:36.48668+00:00
-- url     : https://prove2.me/theorems/778267b7-b34b-4f24-b64a-b3a5d53b958a
-- title:
--   Order Expander: greatest good chain
-- statement:
--   The Order Expander construction uses the greatest good chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L221-L239
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L221-L239

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]

theorem OrderExpander.greatest_good_chain : Good (U (α := α)) := by sorry
