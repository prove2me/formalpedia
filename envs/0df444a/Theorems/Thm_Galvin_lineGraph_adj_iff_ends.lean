-- Prove2me | Theorems.Thm_Galvin_lineGraph_adj_iff_ends
-- name    : Galvin.lineGraph_adj_iff_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:50:17.00415+00:00
-- url     : https://prove2.me/theorems/502cbd71-8f62-4152-9cb9-51f5d738aea7
-- title:
--   Galvin: line Graph adj iff ends
-- statement:
--   The Galvin construction uses the line Graph adj iff ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L82-L99
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L82-L99

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem Galvin.lineGraph_adj_iff_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (endA c e = endA c f ∨ endB c e = endB c f) := by sorry
