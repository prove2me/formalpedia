-- Prove2me | Theorems.Thm_NashWilliams_two_mul_le_cut_edgeEnds
-- name    : NashWilliams.two_mul_le_cut_edgeEnds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:16:38.96716+00:00
-- url     : https://prove2.me/theorems/08750734-af28-4480-93bc-33151425f64a
-- title:
--   Nash Williams: two mul le cut edge Ends
-- statement:
--   A `2k`-edge-connected simple graph has every edge cut of size at least `2k`.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L108-L134
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L108-L134

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)

theorem NashWilliams.two_mul_le_cut_edgeEnds [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (hG : G.IsEdgeConnected (2 * k)) {S : Finset V}
    (hne : S.Nonempty) (hneT : S ≠ Finset.univ) : 2 * k ≤ cut (edgeEnds G) S := by sorry
