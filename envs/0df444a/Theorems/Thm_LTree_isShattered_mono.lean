-- Prove2me | Theorems.Thm_LTree_isShattered_mono
-- name    : LTree.isShattered_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:05.196406+00:00
-- url     : https://prove2.me/theorems/800bd2a5-c8d3-4049-9505-263a8144e89f
-- title:
--   LTree: is Shattered mono
-- statement:
--   Shattering is upward-monotone in the concept class.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L64-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L64-L73

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem LTree.isShattered_mono {X : Type} {n : ℕ} (T : LTree X n)
    {C C' : ConceptClass X Bool} (h : C ⊆ C') :
    T.isShattered C → T.isShattered C' := by sorry
