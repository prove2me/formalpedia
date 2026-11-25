-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
-- name    : GalvinMultigraph.Gadget.lists_innerEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:37:41.036726+00:00
-- url     : https://prove2.me/theorems/de07ae75-4e29-4c4f-a80c-eeb17d2c0dd9
-- title:
--   Gadget: lists inner Edge
-- statement:
--   The Gadget construction uses the lists inner Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L106-L110
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L106-L110

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]

theorem GalvinMultigraph.Gadget.lists_innerEdge (a : E → A) (b : E → B) (P : E → Finset Color)
    (e : E) (i j : Fin k) (h : i ≠ 0 ∨ j ≠ 0) :
    lists a b P (innerEdge a b e i j h) = P e := by sorry
