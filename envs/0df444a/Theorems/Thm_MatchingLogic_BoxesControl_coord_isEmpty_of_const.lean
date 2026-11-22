-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_coord_isEmpty_of_const
-- name    : MatchingLogic.BoxesControl.coord_isEmpty_of_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:00.397478+00:00
-- url     : https://prove2.me/theorems/328c0adf-9f7a-44b2-a8cb-43a3920da3a8
-- title:
--   Boxes Control: coord is Empty of const
-- statement:
--   A constants-only signature has no coordinates at all, so `E* = {ε}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L47-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L47-L50

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

theorem MatchingLogic.BoxesControl.coord_isEmpty_of_const : IsEmpty (Coord SgConst) := by sorry
