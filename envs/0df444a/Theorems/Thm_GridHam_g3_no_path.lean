-- Prove2me | Theorems.Thm_GridHam_g3_no_path
-- name    : GridHam.g3_no_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:13:32.606707+00:00
-- url     : https://prove2.me/theorems/1dda8119-4a51-43b3-bc4b-12ae0d509273
-- title:
--   Grid Ham: g3 no path
-- statement:
--   The case-3 pattern on a 3-high grid of width `m` has no Hamiltonian path.
--   Whichever endpoint has colour 1 is the left one; it plays `u` in
--   `obs_no_path` (for `t`, through the reversed path).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L282-L293
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L282-L293

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.g3_no_path (m sx sy tx ty : ℕ) (hs : sx < m ∧ sy < 3) (ht : tx < m ∧ ty < 3)
    (hg : G3 m sx tx sy ((sx + sy) % 2) ((tx + ty) % 2)) :
    ¬ HasHamPath m 3 (sx, sy) (tx, ty) := by sorry
