-- Prove2me | Theorems.Thm_IsSegment_of_Subset
-- name    : IsSegment_of_Subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:27.670519+00:00
-- url     : https://prove2.me/theorems/1aef5c0d-d407-53c0-8bfe-43aa115788a7
-- title:
--   Is Segment of Subset: Is Segment of Subset
-- statement:
--   A subset `S` of an initial segment `D` of `U`, which is also an initial segment of `U`,
--   is an inital segment of `D`.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L96-L98
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L96-L98

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]

theorem IsSegment_of_Subset (D U S : Set α) (hDU : D ⊆ U) (hSU : S ⊑ U)
    (sub : S ⊆ D) : S ⊑ D := by sorry
