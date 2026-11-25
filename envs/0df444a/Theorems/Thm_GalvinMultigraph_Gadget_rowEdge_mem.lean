-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_rowEdge_mem
-- name    : GalvinMultigraph.Gadget.rowEdge_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:10.185523+00:00
-- url     : https://prove2.me/theorems/cc7b2629-9637-426e-a10a-de57860e37d1
-- title:
--   Gadget: row Edge mem
-- statement:
--   The Gadget construction uses the row Edge mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L129-L134
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L129-L134

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

theorem GalvinMultigraph.Gadget.rowEdge_mem (a : E → A) (b : E → B) (e : E) (i j : Fin k) :
    Sum.inl (Sum.inr (e, i)) ∈ (rowEdge a b e i j).val := by sorry
