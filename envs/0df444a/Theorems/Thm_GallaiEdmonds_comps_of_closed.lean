-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_of_closed
-- name    : GallaiEdmonds.comps_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:43.049069+00:00
-- url     : https://prove2.me/theorems/0764ae5e-69f7-40d6-9a6b-d69fddc99eb4
-- title:
--   Gallai Edmonds: comps of closed
-- statement:
--   The Gallai Edmonds construction uses the comps of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L124-L132
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L124-L132

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

theorem GallaiEdmonds.comps_of_closed (hW : W' ⊆ W) (hc : Closed G W W') :
    comps G W' = {K | K ∈ comps G W ∧ K ⊆ W'} := by sorry
