-- Prove2me | Theorems.Thm_OrderClosures_one_add_le_add_one_ordinal
-- name    : OrderClosures.one_add_le_add_one_ordinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:10.459323+00:00
-- url     : https://prove2.me/theorems/80703667-7c8d-4894-a745-2b3e0a9d412b
-- title:
--   Order Closures: one add le add one ordinal
-- statement:
--   Supplies the ordinal successor inequality needed to choose the component
--   whose strict stage witnesses a prescribed global stage.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L462-L473
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L462-L473

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.one_add_le_add_one_ordinal (δ : Ordinal.{u}) :
    1 + δ ≤ δ + 1 := by sorry
