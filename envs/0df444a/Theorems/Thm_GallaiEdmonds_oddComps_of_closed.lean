-- Prove2me | Theorems.Thm_GallaiEdmonds_oddComps_of_closed
-- name    : GallaiEdmonds.oddComps_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:26.923453+00:00
-- url     : https://prove2.me/theorems/9cffa255-f537-4ea8-a79e-3ed1b8f74df6
-- title:
--   Gallai Edmonds: odd Comps of closed
-- statement:
--   The Gallai Edmonds construction uses the odd Comps of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L134-L138
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L134-L138

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}

theorem GallaiEdmonds.oddComps_of_closed (hW : W' ⊆ W) (hc : Closed G W W') :
    oddComps G W' = {K | K ∈ oddComps G W ∧ K ⊆ W'} := by sorry
