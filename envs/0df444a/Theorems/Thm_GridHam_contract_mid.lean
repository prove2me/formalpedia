-- Prove2me | Theorems.Thm_GridHam_contract_mid
-- name    : GridHam.contract_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:10:51.515799+00:00
-- url     : https://prove2.me/theorems/a13eb2ee-a1d9-4530-aa63-a3cfe5631b21
-- title:
--   Grid Ham: contract mid
-- statement:
--   **Middle contraction.** If a path on a 3-high grid contains a block `M`,
--   exactly the cells of columns 0–1, between two adjacent cells `a` and `b`,
--   then removing `M` and shifting two columns left gives a Hamiltonian path of the
--   grid two columns narrower.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L586-L660
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L586-L660

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.contract_mid (w : ℕ) (u v a b : Coord) (L M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hab : Adjacent a b)
    (hvp : ValidPath w 3 u v (L ++ a :: (M ++ b :: R))) :
    ValidPath (w - 2) 3 (shiftL2 u) (shiftL2 v) ((L ++ a :: b :: R).map shiftL2) := by sorry
