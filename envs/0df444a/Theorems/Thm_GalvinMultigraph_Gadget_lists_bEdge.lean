-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
-- name    : GalvinMultigraph.Gadget.lists_bEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:37:31.908262+00:00
-- url     : https://prove2.me/theorems/b633c2b7-e474-419e-ba3c-fceecb22de6c
-- title:
--   Gadget: lists b Edge
-- statement:
--   The Gadget construction uses the lists b Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L103-L104
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L103-L104

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

theorem GalvinMultigraph.Gadget.lists_bEdge (a : E → A) (b : E → B) (P : E → Finset Color) (e : E) :
    lists a b P (bEdge (k := k) a b e) = P e := by sorry

attribute [defeq] GalvinMultigraph.Gadget.lists_bEdge
