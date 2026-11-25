-- Prove2me | Theorems.Thm_Galvin_card_arc_lt
-- name    : Galvin.card_arc_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:30.329802+00:00
-- url     : https://prove2.me/theorems/358f6058-05c8-4ccb-bdce-904e4620ea05
-- title:
--   Galvin: card arc lt
-- statement:
--   Every out-degree of Galvin's orientation is less than `Δ`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L113-L141
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L113-L141

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

theorem Galvin.card_arc_lt [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by sorry
