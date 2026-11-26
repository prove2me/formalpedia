-- Prove2me | Theorems.Thm_OrderExpander_comparability
-- name    : OrderExpander.comparability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:29.179508+00:00
-- url     : https://prove2.me/theorems/0408b6c9-0065-5783-ae77-05ffbe71984c
-- title:
--   Order Expander: comparability
-- statement:
--   The Order Expander construction uses the comparability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L176-L190
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L176-L190

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]

theorem OrderExpander.comparability (C D : Set α) (goodC : Good C) (goodD : Good D) :
    C ⊑ D ∨ D ⊑ C := by sorry
