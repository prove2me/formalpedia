-- Prove2me | Theorems.Thm_GridHam_extend_right_up
-- name    : GridHam.extend_right_up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:00:22.563324+00:00
-- url     : https://prove2.me/theorems/41dd1e05-ec24-4246-a4ca-825df1194b1f
-- title:
--   Grid Ham: extend right up
-- statement:
--   **Strip extension (edge going up).** A Hamiltonian path on `w × h` with
--   consecutive vertices `(w-1, y), (w-1, y+1)` extends to one on `(w+2) × h`
--   with the same endpoints, by inserting `rightDetour w h y` between them.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L832-L890
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L832-L890

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.extend_right_up (w h : ℕ) (s t : Coord) (l1 l2 : List Coord) (y : ℕ) (hw : 1 ≤ w)
    (hv : ValidPath w h s t (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2)) :
    ValidPath (w + 2) h s t (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) := by sorry
