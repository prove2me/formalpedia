-- Prove2me | Theorems.Thm_OrderClosures_cnfValue_append_lt_append
-- name    : OrderClosures.cnfValue_append_lt_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:31.7829+00:00
-- url     : https://prove2.me/theorems/cf7f1223-0540-4ca2-a76f-5e22c329929f
-- title:
--   Order Closures: cnf Value append lt append
-- statement:
--   Compares values of lists with the same valid prefix; used to show that
--   CNF-list extension implies ordinary ordinal inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L408-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L408-L416

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

theorem OrderClosures.cnfValue_append_lt_append
    (pre l l' : List (Ordinal.{u} × Ordinal.{u}))
    (h : cnfValue l < cnfValue l') :
    cnfValue (pre ++ l) < cnfValue (pre ++ l') := by sorry
