-- Prove2me | Theorems.Thm_GridHam_forbiddenCase1_implies_no_path
-- name    : GridHam.forbiddenCase1_implies_no_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:52:16.382558+00:00
-- url     : https://prove2.me/theorems/55fbd00f-ec14-40c5-8b7d-f290d18072f8
-- title:
--   Grid Ham: forbidden Case1 implies no path
-- statement:
--   **Forbidden case 1 is really forbidden.** On a width-1 (or height-1)
--   grid, the free coordinate of a Hamiltonian path, read in order, is a `Nodup`
--   unit-step chain covering `[0, n-1]`, so by `unitChain_endpoints` the path
--   runs corner to corner.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L337-L488
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L337-L488

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase1_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h1 : width = 1 ∨ height = 1) (hf : ForbiddenCase1 width height s t) :
    ¬ HasHamPath width height s t := by sorry
