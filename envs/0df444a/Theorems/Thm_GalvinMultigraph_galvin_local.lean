-- Prove2me | Theorems.Thm_GalvinMultigraph_galvin_local
-- name    : GalvinMultigraph.galvin_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:07.521153+00:00
-- url     : https://prove2.me/theorems/702f7ccb-37a8-4aa0-94ae-b235d78773f1
-- title:
--   Galvin Multigraph: galvin local
-- statement:
--   **Borodin–Kostochka–Woodall (1997).** In a finite bipartite multigraph, lists whose size at
--   each edge is at least the larger degree of its two ends admit a proper list edge colouring.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Bridge.lean#L29-L61
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Bridge.lean#L29-L61

module
public import Definitions.Def_GalvinMultigraph_Main
public import Definitions.Def_GalvinMultigraph_Local_Main
public import Definitions.Def_GalvinMultigraph_Local_Bridge
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}

theorem GalvinMultigraph.galvin_local [Finite A] [Finite B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, max (Nat.card {f // a f = a e}) (Nat.card {f // b f = b e}) ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by sorry
