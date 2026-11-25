-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_rowColor_injective
-- name    : GalvinMultigraph.Gadget.rowColor_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:09.718374+00:00
-- url     : https://prove2.me/theorems/079be8a5-4502-4e47-8977-5f87248d1265
-- title:
--   Gadget: row Color injective
-- statement:
--   The Gadget construction uses the row Color injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L257-L262
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L257-L262

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

theorem GalvinMultigraph.Gadget.rowColor_injective (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (i : Fin k) :
    Function.Injective (fun j => col (rowEdge a b e i j)) := by sorry
