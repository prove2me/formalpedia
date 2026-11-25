-- Prove2me | Theorems.Thm_NashWilliams_toDigraph_toSimpleGraphInclusive
-- name    : NashWilliams.toDigraph_toSimpleGraphInclusive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:16:26.237441+00:00
-- url     : https://prove2.me/theorems/2350f3b1-e992-5c9f-bdf6-08c5a2bfa4af
-- title:
--   Nash Williams: to Digraph to Simple Graph Inclusive
-- statement:
--   The Nash Williams construction uses the to Digraph to Simple Graph Inclusive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L148-L167
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L148-L167

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

theorem NashWilliams.toDigraph_toSimpleGraphInclusive (o : G.edgeSet → Bool) :
    (toDigraph G o).toSimpleGraphInclusive = G := by sorry
