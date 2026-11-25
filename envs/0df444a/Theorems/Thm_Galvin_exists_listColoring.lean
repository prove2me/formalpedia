-- Prove2me | Theorems.Thm_Galvin_exists_listColoring
-- name    : Galvin.exists_listColoring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:46:56.826534+00:00
-- url     : https://prove2.me/theorems/757e075b-3f9b-474d-9131-4936afe17a48
-- title:
--   Galvin: exists list Coloring
-- statement:
--   **Kernel lemma.** If every finite set of vertices has a kernel and every list is longer than
--   the out-degree of its vertex, there is a proper list colouring.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Kernel.lean#L105-L122
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Kernel.lean#L105-L122

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_GalvinLib_Kernel
set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset

theorem Galvin.exists_listColoring {α Color : Type*} [Fintype α]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D)
    (L : α → Finset Color)
    (hL : ∀ x, (Finset.univ.filter (D x ·)).card < (L x).card) :
    ∃ c : G.Coloring Color, ∀ x, c x ∈ L x := by sorry
