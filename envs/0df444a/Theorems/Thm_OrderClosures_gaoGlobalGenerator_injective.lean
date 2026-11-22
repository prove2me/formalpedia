-- Prove2me | Theorems.Thm_OrderClosures_gaoGlobalGenerator_injective
-- name    : OrderClosures.gaoGlobalGenerator_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:12.88853+00:00
-- url     : https://prove2.me/theorems/c8f53feb-e0e0-4301-9f72-8da148e48181
-- title:
--   Order Closures: gao Global Generator injective
-- statement:
--   Proves that distinct indices give distinct global generators; used for the
--   lower bound on the generator cardinal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L544-L549
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L544-L549

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

theorem OrderClosures.gaoGlobalGenerator_injective
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Function.Injective (gaoGlobalGenerator κ hκ) := by sorry
