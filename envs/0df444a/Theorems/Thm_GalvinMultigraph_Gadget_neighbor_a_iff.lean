-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_neighbor_a_iff
-- name    : GalvinMultigraph.Gadget.neighbor_a_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:21.949886+00:00
-- url     : https://prove2.me/theorems/5c234b97-fc4d-40a7-8bfe-d3be67fc9581
-- title:
--   Gadget: neighbor a iff
-- statement:
--   The Gadget construction uses the neighbor a iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L146-L150
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L146-L150

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

theorem GalvinMultigraph.Gadget.neighbor_a_iff (a : E → A) (b : E → B) (x : A) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inl (Sum.inl x)) v ↔
      ∃ e, a e = x ∧ v = Sum.inr (Sum.inr (e, 0)) := by sorry
