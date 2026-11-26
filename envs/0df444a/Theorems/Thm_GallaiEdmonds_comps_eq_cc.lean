-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_eq_cc
-- name    : GallaiEdmonds.comps_eq_cc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:15.113957+00:00
-- url     : https://prove2.me/theorems/2167817c-883d-4200-a25b-a13c3ed66e0a
-- title:
--   Gallai Edmonds: comps eq cc
-- statement:
--   The Gallai Edmonds construction uses the comps eq cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L113-L114
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L113-L114

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

theorem GallaiEdmonds.comps_eq_cc {K : Set V} (hK : K ∈ comps G W) (hy : y ∈ K) : K = cc G W y := by sorry
