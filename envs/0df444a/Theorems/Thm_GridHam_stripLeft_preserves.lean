-- Prove2me | Theorems.Thm_GridHam_stripLeft_preserves
-- name    : GridHam.stripLeft_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:46.356288+00:00
-- url     : https://prove2.me/theorems/8984cada-57d2-4d33-8914-f50716f7c3d7
-- title:
--   Grid Ham: strip Left preserves
-- statement:
--   **Stripping the leftmost two columns**, by reflecting `stripRight_preserves`.
--   The smaller problem is stated in coordinates shifted left by 2.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1120-L1186
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1120-L1186

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.stripLeft_preserves (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.1) (ht : 2 ≤ t.1)
    (hfree : ∃ y, y < height ∧ (2, y) ≠ s ∧ (2, y) ≠ t)
    (h : HasHamPath (width - 2) height (s.1 - 2, s.2) (t.1 - 2, t.2)) :
    HasHamPath width height s t := by sorry
