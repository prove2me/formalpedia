-- Prove2me | Theorems.Thm_OrderClosures_cnfValue_append
-- name    : OrderClosures.cnfValue_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:07.3517+00:00
-- url     : https://prove2.me/theorems/9ef401d3-450e-427a-b077-0cc236a02209
-- title:
--   Order Closures: cnf Value append
-- statement:
--   Computes the ordinal represented by concatenated CNF lists; used in the
--   later comparison lemmas for common prefixes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L63-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L63-L71

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

theorem OrderClosures.cnfValue_append
    (l m : List (Ordinal.{u} × Ordinal.{u})) :
    cnfValue (l ++ m) = cnfValue l + cnfValue m := by sorry
