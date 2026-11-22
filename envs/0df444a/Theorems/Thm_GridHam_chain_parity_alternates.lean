-- Prove2me | Theorems.Thm_GridHam_chain_parity_alternates
-- name    : GridHam.chain_parity_alternates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:16:55.917237+00:00
-- url     : https://prove2.me/theorems/8f7c1b81-0898-4781-adf8-4050ccd71ad6
-- title:
--   Grid Ham: chain parity alternates
-- statement:
--   Along a chain of adjacent vertices, parity strictly alternates: the
--   parity at position `i` is `(parity of position 0) + i`, mod 2. Proved by
--   induction on the list, peeling one adjacency step at a time.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L41-L74
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L41-L74

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chain_parity_alternates (p : List Coord) (hc : chainAdjacent p = true) :
    ∀ i (hi : i < p.length) (h0 : 0 < p.length),
      parity (p.get ⟨i, hi⟩) = (parity (p.get ⟨0, h0⟩) + i) % 2 := by sorry
