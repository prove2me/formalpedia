-- Prove2me | Theorems.Thm_OrderClosures_gaoProductProjection_orderAdherence
-- name    : OrderClosures.gaoProductProjection_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:57.578608+00:00
-- url     : https://prove2.me/theorems/044c3325-80cf-452e-9c1d-6dcd94c567e3
-- title:
--   Order Closures: gao Product Projection order Adherence
-- statement:
--   Transfers membership in order adherence through product projection; used
--   in the inductive comparison of global and component stages.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L307-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L307-L313

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

theorem OrderClosures.gaoProductProjection_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoIterationProduct κ)) :
    gaoProductProjection κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductProjection κ β '' A) := by sorry
