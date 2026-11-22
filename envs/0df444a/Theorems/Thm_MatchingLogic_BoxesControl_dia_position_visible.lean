-- Prove2me | Theorems.Thm_MatchingLogic_BoxesControl_dia_position_visible
-- name    : MatchingLogic.BoxesControl.dia_position_visible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:10.189595+00:00
-- url     : https://prove2.me/theorems/0e9297b4-075c-43b1-8cc7-f407bd06d060
-- title:
--   Boxes Control: dia position visible
-- statement:
--   **A position swap in `dia` is observable.**  If `dia` put its argument in
--   the wrong slot, this would fail.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L81-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean#L81-L104

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

theorem MatchingLogic.BoxesControl.dia_position_visible :
    Mo.denote (fun _ => (2 : Fin 4)) (dia e0 (.var 0)) ≠
      Mo.denote (fun _ => (2 : Fin 4)) (dia e1 (.var (0 : Nat))) := by sorry
