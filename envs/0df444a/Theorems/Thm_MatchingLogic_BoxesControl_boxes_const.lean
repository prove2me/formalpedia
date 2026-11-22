-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_boxes_const
-- name    : MatchingLogic.BoxesControl.boxes_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:04.339088+00:00
-- url     : https://prove2.me/theorems/9891391b-b6a9-4e7d-aa3d-7ea9d4b85c1a
-- title:
--   Boxes Control: boxes const
-- statement:
--   Consequently boxing is trivial there: the only word is `ε`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L53-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L53-L57

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

theorem MatchingLogic.BoxesControl.boxes_const (p : List (Coord SgConst)) (ψ : Pattern SgConst Nat) :
    boxes p ψ = ψ := by sorry
