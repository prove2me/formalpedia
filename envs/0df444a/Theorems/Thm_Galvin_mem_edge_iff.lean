-- Prove2me | Theorems.Thm_Galvin_mem_edge_iff
-- name    : Galvin.mem_edge_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:12.79371+00:00
-- url     : https://prove2.me/theorems/45b55fd8-396b-4384-a060-5b4c8d97aad9
-- title:
--   Galvin: mem edge iff
-- statement:
--   The Galvin construction uses the mem edge iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L78-L80
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L78-L80

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

theorem Galvin.mem_edge_iff (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = endA c e ∨ v = endB c e := by sorry
