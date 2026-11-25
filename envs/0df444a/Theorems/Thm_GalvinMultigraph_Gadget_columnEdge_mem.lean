-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_columnEdge_mem
-- name    : GalvinMultigraph.Gadget.columnEdge_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:11.517265+00:00
-- url     : https://prove2.me/theorems/c528c89c-f342-49f0-86ca-17c26e3edf1d
-- title:
--   Gadget: column Edge mem
-- statement:
--   The Gadget construction uses the column Edge mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L142-L144
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L142-L144

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

theorem GalvinMultigraph.Gadget.columnEdge_mem (a : E → A) (b : E → B) (e : E) (i j : Fin k) (hj : j ≠ 0) :
    Sum.inr (Sum.inr (e, j)) ∈ (rowEdge a b e i j).val := by sorry
