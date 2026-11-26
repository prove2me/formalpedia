-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_subset
-- name    : GallaiEdmonds.comps_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:07.339458+00:00
-- url     : https://prove2.me/theorems/48f54e43-f831-5314-b04d-df56f27162b6
-- title:
--   Gallai Edmonds: comps subset
-- statement:
--   The Gallai Edmonds construction uses the comps subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L107-L108
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L107-L108

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

theorem GallaiEdmonds.comps_subset {K : Set V} (hK : K ∈ comps G W) : K ⊆ W := by sorry
