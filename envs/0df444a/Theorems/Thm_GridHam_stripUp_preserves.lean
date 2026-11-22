-- Prove2me | Theorems.Thm_GridHam_stripUp_preserves
-- name    : GridHam.stripUp_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:30:46.37198+00:00
-- url     : https://prove2.me/theorems/97b013b9-ca0e-41ac-a659-8531e93c9dc8
-- title:
--   Grid Ham: strip Up preserves
-- statement:
--   **Stripping the top two rows**, by transposing `stripRight_preserves`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L967-L977
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L967-L977

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.stripUp_preserves (width height : ℕ) (s t : Coord)
    (hs : s.2 + 2 < height) (ht : t.2 + 2 < height)
    (hfree : ∃ x, x < width ∧ (x, height - 3) ≠ s ∧ (x, height - 3) ≠ t)
    (h : HasHamPath width (height - 2) s t) :
    HasHamPath width height s t := by sorry
