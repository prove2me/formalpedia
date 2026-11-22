-- Prove2me | Theorems.Thm_OrderClosures_CNFListLT_upper_trichotomy
-- name    : OrderClosures.CNFListLT.upper_trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:32.300107+00:00
-- url     : https://prove2.me/theorems/f903b0ec-4e4a-41b5-9a24-dbe85e7055de
-- title:
--   CNFList LT: upper trichotomy
-- statement:
--   Shows that two CNF lists extending a fixed list are comparable; used for
--   linearity of upper cones in the ordinal extension order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L598-L660
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L598-L660

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

theorem OrderClosures.CNFListLT.upper_trichotomy
    {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hln : CNFListLT l n) :
    m = n ∨ CNFListLT m n ∨ CNFListLT n m := by sorry
