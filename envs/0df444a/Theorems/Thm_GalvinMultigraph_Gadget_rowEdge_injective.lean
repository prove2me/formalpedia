-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_rowEdge_injective
-- name    : GalvinMultigraph.Gadget.rowEdge_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:58.727869+00:00
-- url     : https://prove2.me/theorems/2f856031-65cf-4d84-97d8-5df92a014c48
-- title:
--   Gadget: row Edge injective
-- statement:
--   The Gadget construction uses the row Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L118-L127
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L118-L127

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

theorem GalvinMultigraph.Gadget.rowEdge_injective (a : E → A) (b : E → B) (e : E) (i : Fin k) :
    Function.Injective (rowEdge a b e i) := by sorry
