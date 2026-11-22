-- Prove2me | Theorems.Thm_GridHam_stripDown_preserves
-- name    : GridHam.stripDown_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:34:06.025057+00:00
-- url     : https://prove2.me/theorems/befbfeef-ab02-435e-8fa3-3bfaf7549ade
-- title:
--   Grid Ham: strip Down preserves
-- statement:
--   **Stripping the bottom two rows**, by transposing `stripLeft_preserves`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1189-L1199
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1189-L1199

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.stripDown_preserves (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.2) (ht : 2 ≤ t.2)
    (hfree : ∃ x, x < width ∧ (x, 2) ≠ s ∧ (x, 2) ≠ t)
    (h : HasHamPath width (height - 2) (s.1, s.2 - 2) (t.1, t.2 - 2)) :
    HasHamPath width height s t := by sorry
