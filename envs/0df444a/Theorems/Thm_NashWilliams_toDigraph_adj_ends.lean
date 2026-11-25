-- Prove2me | Theorems.Thm_NashWilliams_toDigraph_adj_ends
-- name    : NashWilliams.toDigraph_adj_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:06:47.723934+00:00
-- url     : https://prove2.me/theorems/c7fbe275-ebc7-49bb-9f93-e949541af6aa
-- title:
--   Nash Williams: to Digraph adj ends
-- statement:
--   The Nash Williams construction uses the to Digraph adj ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L140-L146
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L140-L146

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

theorem NashWilliams.toDigraph_adj_ends {o : G.edgeSet → Bool} {a b : V} (h : (toDigraph G o).Adj a b) :
    ∃ e : G.edgeSet, edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a) := by sorry
