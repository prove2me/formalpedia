-- Prove2me | Theorems.Thm_NashWilliams_toDigraph_antisymm
-- name    : NashWilliams.toDigraph_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:17:41.040484+00:00
-- url     : https://prove2.me/theorems/1a80671b-f6f4-4989-b375-6e69e61d617a
-- title:
--   Nash Williams: to Digraph antisymm
-- statement:
--   The Nash Williams construction uses the to Digraph antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L169-L192
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L169-L192

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

theorem NashWilliams.toDigraph_antisymm (o : G.edgeSet → Bool) (a b : V) (h : (toDigraph G o).Adj a b) :
    ¬ (toDigraph G o).Adj b a := by sorry
