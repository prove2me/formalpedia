-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
-- name    : GalvinMultigraph.Gadget.lists_aEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:37:36.427751+00:00
-- url     : https://prove2.me/theorems/b089eac3-591b-4efd-85f9-6d825c967819
-- title:
--   Gadget: lists a Edge
-- statement:
--   The Gadget construction uses the lists a Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L100-L101
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L100-L101

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

theorem GalvinMultigraph.Gadget.lists_aEdge (a : E → A) (b : E → B) (P : E → Finset Color) (e : E) :
    lists a b P (aEdge (k := k) a b e) = P e := by sorry

attribute [defeq] GalvinMultigraph.Gadget.lists_aEdge
