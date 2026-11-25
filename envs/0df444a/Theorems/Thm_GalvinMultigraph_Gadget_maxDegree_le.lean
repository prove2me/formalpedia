-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_maxDegree_le
-- name    : GalvinMultigraph.Gadget.maxDegree_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:50.691203+00:00
-- url     : https://prove2.me/theorems/fff1d83f-fa8b-44c5-b2b6-c55eb9850d46
-- title:
--   Gadget: max Degree le
-- statement:
--   The Gadget construction uses the max Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L224-L236
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L224-L236

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

theorem GalvinMultigraph.Gadget.maxDegree_le [Fintype A] [Fintype B] [Fintype E]
    (a : E → A) (b : E → B)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k) : (graph (k := k) a b).maxDegree ≤ k := by sorry
