-- Prove2me | Theorems.Thm_GridHam_interior_two
-- name    : GridHam.interior_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:31:46.744225+00:00
-- url     : https://prove2.me/theorems/03593b56-e547-4663-8799-a5a526470a09
-- title:
--   Grid Ham: interior two
-- statement:
--   A middle cell has a predecessor and a successor, and they differ.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L132-L161
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L132-L161

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.interior_two {p : List Coord} {x : Coord} (hnd : p.Nodup) (hx : x ∈ p)
    (hh : p.head? ≠ some x) (hl : p.getLast? ≠ some x) :
    ∃ a b, a ≠ b ∧ PNext p a x ∧ PNext p x b := by sorry
