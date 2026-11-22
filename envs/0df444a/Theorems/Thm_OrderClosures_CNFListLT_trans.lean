-- Prove2me | Theorems.Thm_OrderClosures_CNFListLT_trans
-- name    : OrderClosures.CNFListLT.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:06.500456+00:00
-- url     : https://prove2.me/theorems/e58cb780-741b-4748-9111-044b3f6b664c
-- title:
--   CNFList LT: trans
-- statement:
--   Lifts one-step transitivity to the transitive closure `CNFListLT`; used to
--   prove that `cnfExtensionLE` is a partial order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L564-L594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L564-L594

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

theorem OrderClosures.CNFListLT.trans {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hmn : CNFListLT m n) : CNFListLT l n := by sorry
