-- Prove2me | Theorems.Thm_GridHam_cnt1_grid
-- name    : GridHam.cnt1_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:25:44.048818+00:00
-- url     : https://prove2.me/theorems/2b535b93-12a6-405f-9000-ee2cbe683795
-- title:
--   Grid Ham: cnt1 grid
-- statement:
--   For odd `h`: `2 · (colour-1 cells of the w × h grid) + w % 2 = w · h`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L249-L255
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L249-L255

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.cnt1_grid (h : ℕ) (hh : h % 2 = 1) : ∀ w, 2 * cnt1 (allCoords w h) + w % 2 = w * h := by sorry
