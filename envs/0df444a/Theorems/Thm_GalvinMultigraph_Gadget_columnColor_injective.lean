-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_columnColor_injective
-- name    : GalvinMultigraph.Gadget.columnColor_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:13.9208+00:00
-- url     : https://prove2.me/theorems/5fb35607-03b5-4ab1-b8b6-f5c7e62aab56
-- title:
--   Gadget: column Color injective
-- statement:
--   The Gadget construction uses the column Color injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L264-L269
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L264-L269

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

theorem GalvinMultigraph.Gadget.columnColor_injective (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (j : Fin k) (hj : j ≠ 0) :
    Function.Injective (fun i => col (rowEdge a b e i j)) := by sorry
