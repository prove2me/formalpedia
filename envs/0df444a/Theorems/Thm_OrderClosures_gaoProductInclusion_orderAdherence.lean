-- Prove2me | Theorems.Thm_OrderClosures_gaoProductInclusion_orderAdherence
-- name    : OrderClosures.gaoProductInclusion_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:50.940035+00:00
-- url     : https://prove2.me/theorems/57d925bc-7209-4073-8c7f-c65466b8964b
-- title:
--   Order Closures: gao Product Inclusion order Adherence
-- statement:
--   Transfers component order-adherence membership through coordinate
--   inclusion; used for the reverse stage comparison.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L317-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L317-L323

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

theorem OrderClosures.gaoProductInclusion_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoComponent β.1)) :
    gaoProductInclusion κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductInclusion κ β '' A) := by sorry
