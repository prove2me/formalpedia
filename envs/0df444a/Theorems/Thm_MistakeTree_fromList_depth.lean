-- Prove2me | Theorems.Thm_MistakeTree_fromList_depth
-- name    : MistakeTree.fromList_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:34.644162+00:00
-- url     : https://prove2.me/theorems/7c1bc2d2-8eca-425d-ac13-c607aab748a1
-- title:
--   Mistake Tree: from List depth
-- statement:
--   The depth of a mistake tree built from a list of length `n` equals `n`. The basic
--   well-formedness property of the `fromList` constructor: depth tracks list length
--   exactly, so the Littlestone dimension can be read off from a built tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Littlestone.lean#L71-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Littlestone.lean#L71-L77

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem MistakeTree.fromList_depth {X : Type u} :
    ∀ (l : List X), (MistakeTree.fromList l).depth = l.length
  := by sorry
