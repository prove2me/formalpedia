-- Prove2me | Theorems.Thm_GridHam_adjacent_parity_ne
-- name    : GridHam.adjacent_parity_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:23:56.251948+00:00
-- url     : https://prove2.me/theorems/141db2dd-7921-4be1-8150-7c9d5048b8e7
-- title:
--   Grid Ham: adjacent parity ne
-- statement:
--   Adjacent vertices always have different parity: exactly one coordinate
--   changes by exactly 1, so the coordinate sum's parity flips.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L32-L36
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L32-L36

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.adjacent_parity_ne {v w : Coord} (h : Adjacent v w) :
    parity v ≠ parity w := by sorry
