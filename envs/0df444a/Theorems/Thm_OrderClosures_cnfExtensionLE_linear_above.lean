-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLE_linear_above
-- name    : OrderClosures.cnfExtensionLE_linear_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:46.641195+00:00
-- url     : https://prove2.me/theorems/31ed65fa-2c9a-48be-96b1-76d44f793b6a
-- title:
--   Order Closures: cnf Extension LE linear above
-- statement:
--   Includes equality in upper-cone comparability; used when minimal Gao
--   dominators must be compared in `StageFormula`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L721-L732
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L721-L732

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnfExtensionLE_linear_above (ζ : Ordinal.{u})
    {η η' : Ordinal.{u}} (hη : cnfExtensionLE ζ η)
    (hη' : cnfExtensionLE ζ η') :
    cnfExtensionLE η η' ∨ cnfExtensionLE η' η := by sorry
