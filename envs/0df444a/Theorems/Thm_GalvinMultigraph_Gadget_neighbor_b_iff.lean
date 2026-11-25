-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_neighbor_b_iff
-- name    : GalvinMultigraph.Gadget.neighbor_b_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:29.150329+00:00
-- url     : https://prove2.me/theorems/2fe53c6d-5b7f-4bf4-b872-12ad10d4658f
-- title:
--   Gadget: neighbor b iff
-- statement:
--   The Gadget construction uses the neighbor b iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L152-L156
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L152-L156

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

theorem GalvinMultigraph.Gadget.neighbor_b_iff (a : E → A) (b : E → B) (y : B) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inr (Sum.inl y)) v ↔
      ∃ e, b e = y ∧ v = Sum.inl (Sum.inr (e, 0)) := by sorry
