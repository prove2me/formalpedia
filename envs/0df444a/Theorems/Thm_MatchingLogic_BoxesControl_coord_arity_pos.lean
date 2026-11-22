-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_coord_arity_pos
-- name    : MatchingLogic.BoxesControl.coord_arity_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:02.872805+00:00
-- url     : https://prove2.me/theorems/e7efd93f-1f5d-4d76-b76b-fd21dfa95aaf
-- title:
--   Boxes Control: coord arity pos
-- statement:
--   Every coordinate has arity at least one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L36-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L36-L38

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

theorem MatchingLogic.BoxesControl.coord_arity_pos (S : Signature) (e : Coord S) : 1 ≤ S.arity e.1 := by sorry
