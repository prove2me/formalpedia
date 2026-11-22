-- Prove2me | Theorems.Thm_GridHam_chain_parity_head_last
-- name    : GridHam.chain_parity_head_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:23:53.802923+00:00
-- url     : https://prove2.me/theorems/6abfaefe-84b9-43eb-a5ee-f51a162b0e7d
-- title:
--   Grid Ham: chain parity head last
-- statement:
--   The head-to-last-element counterpart of `chain_parity_alternates`,
--   proved independently by front-peeling induction (so `List.getLast`, not
--   `List.get` at a computed index, is what shows up -- avoiding the need to
--   separately relate `.get` at the last index to `.getLast`/`.getLast?`, which
--   would just reintroduce the same bridging problem one level down). Combined
--   with `getLast?_eq_getLast_of_ne_nil`, this is what `hamPath_implies_diff_parity_of_even`
--   needs.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L112-L142
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L112-L142

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chain_parity_head_last :
    ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
      ∀ (hne : (a :: l) ≠ []),
        parity ((a :: l).getLast hne) = (parity a + l.length) % 2 := by sorry
