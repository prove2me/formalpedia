-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_reachWord_order_right
-- name    : MatchingLogic.BoxesControl.reachWord_order_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:08.632665+00:00
-- url     : https://prove2.me/theorems/db442469-5d4d-4f15-961e-e19c493d8b8d
-- title:
--   Boxes Control: reach Word order right
-- statement:
--   … and the other.  Together these two force the composition order of
--   `reachWord`, and through Lemma 4 the nesting order of `boxes`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L158-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L158-L161

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Definitions.Def_LeanPool_MatchingLogic_BoxesControl
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.BoxesControl

theorem MatchingLogic.BoxesControl.reachWord_order_right (v : Fin 4) :
    Mo.reachWord [e1, e0] 0 v ↔ v = 2 := by sorry
