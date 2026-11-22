-- Prove2me | Theorems.Thm_MistakeTree_fromList_shattered
-- name    : MistakeTree.fromList_shattered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:35.494601+00:00
-- url     : https://prove2.me/theorems/0f78e501-6401-4262-8fe7-01e874e98cd2
-- title:
--   Mistake Tree: from List shattered
-- statement:
--   A shattered tree can be built from any list of elements from a shattered Finset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Littlestone.lean#L92-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Littlestone.lean#L92-L108

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

theorem MistakeTree.fromList_shattered {X : Type u} [DecidableEq X] {C : ConceptClass X Bool}
    (l : List X) (hl : l.Nodup) (hS : Shatters X C l.toFinset) :
    (MistakeTree.fromList l).isShattered X C := by sorry
