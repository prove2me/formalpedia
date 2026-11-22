-- Prove2me | Theorems.Thm_GridHam_chain_detour
-- name    : GridHam.chain_detour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:59:19.810934+00:00
-- url     : https://prove2.me/theorems/41911c5c-a3a2-4269-be63-dc517c83cb61
-- title:
--   Grid Ham: chain detour
-- statement:
--   The Grid Ham construction uses the chain detour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L807-L827
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L807-L827

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chain_detour (w h y : ℕ) (hw : 1 ≤ w) (hy : y + 1 < h) (l2 : List Coord)
    (hb : chainAdjacent ((w - 1, y + 1) :: l2) = true) :
    chainAdjacent ((w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) = true := by sorry
