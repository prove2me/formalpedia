-- Prove2me | Theorems.Thm_GridHam_acc_iff
-- name    : GridHam.acc_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:33:04.938829+00:00
-- url     : https://prove2.me/theorems/81d24a83-4570-48ca-ab49-3a09cd6db267
-- title:
--   Grid Ham: acc iff
-- statement:
--   **`IsAcceptable` in arithmetic form.**
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L133-L139
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L133-L139

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.acc_iff (w h : ℕ) (s t : Coord) :
    IsAcceptable w h s t ↔ AccA w h s.1 s.2 t.1 t.2 := by sorry
