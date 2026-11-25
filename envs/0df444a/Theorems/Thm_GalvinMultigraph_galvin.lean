-- Prove2me | Theorems.Thm_GalvinMultigraph_galvin
-- name    : GalvinMultigraph.galvin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:22:54.897809+00:00
-- url     : https://prove2.me/theorems/e3e56090-55ba-433c-bd54-b3e1013413fb
-- title:
--   Galvin Multigraph: galvin
-- statement:
--   Galvin (1995): every list assignment of size at least the maximum degree
--   admits a proper edge coloring of the finite bipartite multigraph.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L84-L89
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L84-L89

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_Galvin_galvin

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}

theorem GalvinMultigraph.galvin [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, maxDegree a b ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by sorry
