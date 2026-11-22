-- Prove2me | Theorems.Thm_GridHam_mem_allCoords
-- name    : GridHam.mem_allCoords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:27:54.012583+00:00
-- url     : https://prove2.me/theorems/fea8c842-5d3c-465b-8d71-12ca6ea19dc5
-- title:
--   Grid Ham: mem all Coords
-- statement:
--   `v ∈ allCoords w h` is just "in bounds".
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L29-L36
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L29-L36

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_allCoords (w h : ℕ) (v : Coord) :
    v ∈ allCoords w h ↔ v.1 < w ∧ v.2 < h := by sorry
