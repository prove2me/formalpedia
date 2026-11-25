-- Prove2me | Theorems.Thm_GalvinMultigraph_colorable_iff
-- name    : GalvinMultigraph.colorable_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:58:31.482832+00:00
-- url     : https://prove2.me/theorems/393cdb7e-4d7e-4e77-b204-f1e31140b2c8
-- title:
--   Galvin Multigraph: colorable iff
-- statement:
--   Exact ordinary chromatic-index threshold, including empty edge sets.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L130-L138
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L130-L138

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

theorem GalvinMultigraph.colorable_iff [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ) :
    (∃ c : E → Fin k, Proper a b c) ↔ maxDegree a b ≤ k := by sorry
