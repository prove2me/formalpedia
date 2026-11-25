-- Prove2me | Theorems.Thm_GalvinMultigraph_degree_bounds_of_proper
-- name    : GalvinMultigraph.degree_bounds_of_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:37.653707+00:00
-- url     : https://prove2.me/theorems/5ef70a1d-270a-44a4-a2d2-560a26ffe369
-- title:
--   Galvin Multigraph: degree bounds of proper
-- statement:
--   Every proper finite-palette edge coloring has at least as many colors as
--   each incidence degree.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L100-L120
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L100-L120

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}

theorem GalvinMultigraph.degree_bounds_of_proper [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    (∀ x, Nat.card {e // a e = x} ≤ Fintype.card Color) ∧
    (∀ y, Nat.card {e // b e = y} ≤ Fintype.card Color) := by sorry
