-- Prove2me | Theorems.Thm_GridHam_hamPath_implies_diff_parity_of_even
-- name    : GridHam.hamPath_implies_diff_parity_of_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:23:53.884514+00:00
-- url     : https://prove2.me/theorems/77a733ad-9be2-4f83-9793-6347bbcbc0fe
-- title:
--   Grid Ham: ham Path implies diff parity of even
-- statement:
--   **Necessary condition, color part (even case).** If the grid has an even
--   number of vertices and a Hamiltonian path exists from `s` to `t`, then `s`
--   and `t` have different parity. This direction needs no counting lemma: it
--   follows directly from alternation, since `n - 1` is odd exactly when `n` is
--   even.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L149-L171
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L149-L171

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hamPath_implies_diff_parity_of_even
    (width height : ℕ) (s t : Coord) (heven : (width * height) % 2 = 0)
    (h : HasHamPath width height s t) : parity s ≠ parity t := by sorry
