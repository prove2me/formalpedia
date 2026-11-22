-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_reachWord_order_left
-- name    : MatchingLogic.BoxesControl.reachWord_order_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:06.078164+00:00
-- url     : https://prove2.me/theorems/da5ac9e5-b179-4f03-aba0-a50dd5cb9b1c
-- title:
--   Boxes Control: reach Word order left
-- statement:
--   **The order of a word is observable**, one way …
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L151-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L151-L154

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

theorem MatchingLogic.BoxesControl.reachWord_order_left (v : Fin 4) :
    Mo.reachWord [e0, e1] 0 v ↔ v = 3 := by sorry
