-- Prove2me | Theorems.Thm_OrderClosures_CNFStep_trans
-- name    : OrderClosures.CNFStep.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:03.282231+00:00
-- url     : https://prove2.me/theorems/3b718248-74b7-45cf-8c06-ac245a173d44
-- title:
--   CNFStep: trans
-- statement:
--   Proves transitivity for one-step extensions sharing a prefix; used in the
--   global transitivity proof for `CNFListLT`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L523-L533
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L523-L533

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

theorem OrderClosures.CNFStep.trans {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hyz : CNFStep pre y z) : CNFStep pre x z := by sorry
