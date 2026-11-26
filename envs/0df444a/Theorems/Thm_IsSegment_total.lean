-- Prove2me | Theorems.Thm_IsSegment_total
-- name    : IsSegment_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:32.282795+00:00
-- url     : https://prove2.me/theorems/040bb827-e2f0-547e-92dd-dcb0d3b0656e
-- title:
--   Is Segment total: Is Segment total
-- statement:
--   Segments of a chain are comparable.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L103-L118
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L103-L118

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]

theorem IsSegment_total {A B C : Set α} (hchain : IsChain (· ≤ ·) C) (hA : A ⊑ C) (hB : B ⊑ C) :
    A ⊑ B ∨ B ⊑ A := by sorry
