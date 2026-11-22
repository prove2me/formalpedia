-- Prove2me | Theorems.Thm_GridHam_obs_no_path
-- name    : GridHam.obs_no_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:11:03.178089+00:00
-- url     : https://prove2.me/theorems/79b33f1c-e9eb-479b-baa7-68a54a59e698
-- title:
--   Grid Ham: obs no path
-- statement:
--   **Case-3 obstruction on 3-high grids.** If `u` has colour 1, lies left of
--   `v`, and either `u` is in the middle row or `v` is at least two columns
--   further right, there is no Hamiltonian path from `u` to `v`. Induction on
--   `u.x`: B0 for `u.x = 0`, B1 for `u.x = 1`, and the contraction C1 otherwise.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L977-L1008
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L977-L1008

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.obs_no_path (k : ℕ) : ∀ (w : ℕ) (u v : Coord), u.1 ≤ k → (u.1 + u.2) % 2 = 1 →
    u.2 < 3 → u.1 < v.1 → (u.2 = 1 ∨ u.1 + 1 < v.1) → ¬ HasHamPath w 3 u v := by sorry
