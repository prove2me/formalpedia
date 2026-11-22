-- Prove2me | Theorems.Thm_GridHam_contract_prefix
-- name    : GridHam.contract_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:07:10.437129+00:00
-- url     : https://prove2.me/theorems/1266dd0b-2257-412d-9d1f-966db3bec5b4
-- title:
--   Grid Ham: contract prefix
-- statement:
--   **Prefix contraction.** If a path on a 3-high grid begins with a block `M`
--   that is exactly the cells of columns 0–1, dropping `M` and shifting two
--   columns left gives a Hamiltonian path of the grid two columns narrower.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L274-L337
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L274-L337

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.contract_prefix (w : ℕ) (u v a : Coord) (M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hv : ValidPath w 3 u v (M ++ a :: R)) :
    ValidPath (w - 2) 3 (shiftL2 a) (shiftL2 v) ((a :: R).map shiftL2) := by sorry
