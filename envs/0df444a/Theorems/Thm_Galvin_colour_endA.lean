-- Prove2me | Theorems.Thm_Galvin_colour_endA
-- name    : Galvin.colour_endA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:49:21.809467+00:00
-- url     : https://prove2.me/theorems/d3918ac4-0678-47c9-b7bf-8efeed9d4836
-- title:
--   Galvin: colour end A
-- statement:
--   The Galvin construction uses the colour end A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L57-L58
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L57-L58

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

theorem Galvin.colour_endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endA c e) = 0 := by sorry
