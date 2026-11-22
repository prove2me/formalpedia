-- Prove2me | Theorems.Thm_OrderClosures_mk_gaoGlobalGenerator_range
-- name    : OrderClosures.mk_gaoGlobalGenerator_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:11.816456+00:00
-- url     : https://prove2.me/theorems/aaef1346-5573-4f8d-9c09-7eb09f43e7b8
-- title:
--   Order Closures: mk gao Global Generator range
-- statement:
--   Computes the cardinality of the global generator range; used in the exact
--   calculation of `solidGeneratorNumber`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L553-L564
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L553-L564

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

theorem OrderClosures.mk_gaoGlobalGenerator_range
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) =
      Cardinal.lift.{u + 1, u} κ := by sorry
