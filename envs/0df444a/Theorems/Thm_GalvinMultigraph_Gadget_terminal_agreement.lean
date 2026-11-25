-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_terminal_agreement
-- name    : GalvinMultigraph.Gadget.terminal_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:16.155797+00:00
-- url     : https://prove2.me/theorems/17ec6dfa-5e3a-4e2f-94fc-904271b8a0f0
-- title:
--   Gadget: terminal agreement
-- statement:
--   A k-element palette forces the two terminal edges to have equal colors.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L272-L312
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L272-L312

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

theorem GalvinMultigraph.Gadget.terminal_agreement (a : E → A) (b : E → B) (P : E → Finset Color)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (hcol : ∀ f, col f ∈ lists a b P f) (e : E) (hP : (P e).card = k) :
    col (aEdge a b e) = col (bEdge a b e) := by sorry
