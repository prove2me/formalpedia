-- Prove2me | Theorems.Thm_GridHam_hamPath_odd_parity
-- name    : GridHam.hamPath_odd_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:25:53.040582+00:00
-- url     : https://prove2.me/theorems/7fc8d99b-c02d-43a2-91e7-03241f0b605f
-- title:
--   Grid Ham: ham Path odd parity
-- statement:
--   **Necessary condition, odd case.** On a grid with both sides odd, a
--   Hamiltonian path starts and ends on colour 0. Colours alternate along the
--   path, so starting on colour 1 would visit `(n+1)/2` colour-1 cells, but the
--   grid only has `(n-1)/2` and the path has no repeats.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L261-L283
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L261-L283

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hamPath_odd_parity (width height : ℕ) (s t : Coord)
    (hodd : width % 2 = 1 ∧ height % 2 = 1) (h : HasHamPath width height s t) :
    parity s = 0 ∧ parity t = 0 := by sorry
