-- Prove2me | Theorems.Thm_OrderSelector_good_of_isSegment
-- name    : OrderSelector.good_of_isSegment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:49.725578+00:00
-- url     : https://prove2.me/theorems/c12e9534-393d-45d9-bc6c-8928afd5c769
-- title:
--   Order Selector: good of is Segment
-- statement:
--   Every segment of a good chain is good. The verification of this fact is left to the reader
--   in the proof of Proposition `prop:good-well-ordered` of the paper.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L277-L298
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L277-L298

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

theorem OrderSelector.good_of_isSegment {C D : Set α} (hC : Good C) (hseg : D ⊑ C) : Good D := by sorry
