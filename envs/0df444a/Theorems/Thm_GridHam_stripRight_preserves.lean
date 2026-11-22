-- Prove2me | Theorems.Thm_GridHam_stripRight_preserves
-- name    : GridHam.stripRight_preserves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:39:11.658516+00:00
-- url     : https://prove2.me/theorems/e8667dc3-ac9b-4313-a88c-9abcac906d3e
-- title:
--   Grid Ham: strip Right preserves
-- statement:
--   **Stripping the rightmost two columns.** If the `(width-2) × height`
--   problem is solvable, neither endpoint lies in the two new columns, and some
--   vertex of the smaller grid's rightmost column (`x = width - 3`) is neither
--   `s` nor `t`, then the full problem is solvable. The last hypothesis is what
--   guarantees an edge of the smaller path along that column (degree argument,
--   `exists_col_edge`); without it the statement is false (e.g. `5 × 1`).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L898-L964
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L898-L964

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.stripRight_preserves (width height : ℕ) (s t : Coord)
    (hs : s.1 + 2 < width) (_ht : t.1 + 2 < width)
    (hfree : ∃ y, y < height ∧ (width - 3, y) ≠ s ∧ (width - 3, y) ≠ t)
    (h : HasHamPath (width - 2) height s t) :
    HasHamPath width height s t := by sorry
