-- Prove2me | Theorems.Thm_GridHam_hasHamPath_flipY
-- name    : GridHam.hasHamPath_flipY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:07:54.651278+00:00
-- url     : https://prove2.me/theorems/d0a25fb9-7cad-4b6b-aefd-26b1156ce373
-- title:
--   Grid Ham: has Ham Path flip Y
-- statement:
--   Flip a Hamiltonian path top to bottom (via transpose, reflect, transpose).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L340-L342
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L340-L342

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hasHamPath_flipY {w h : ℕ} {s t : Coord} (hp : HasHamPath w h s t) :
    HasHamPath w h (s.1, h - 1 - s.2) (t.1, h - 1 - t.2) := by sorry
