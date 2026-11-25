-- Prove2me | Theorems.Thm_NashWilliams_mk_edgeEnds
-- name    : NashWilliams.mk_edgeEnds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:05:02.1273+00:00
-- url     : https://prove2.me/theorems/412c6a55-717f-5d55-8cf5-d5f2dc4a22da
-- title:
--   Nash Williams: mk edge Ends
-- statement:
--   The Nash Williams construction uses the mk edge Ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L85-L86
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L85-L86

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

theorem NashWilliams.mk_edgeEnds (e : G.edgeSet) : s((edgeEnds G e).1, (edgeEnds G e).2) = (e : Sym2 V) := by sorry
