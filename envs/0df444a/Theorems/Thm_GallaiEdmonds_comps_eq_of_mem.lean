-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_eq_of_mem
-- name    : GallaiEdmonds.comps_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:10.699825+00:00
-- url     : https://prove2.me/theorems/a5b798b2-12c9-5db9-8804-c848c89c4a2f
-- title:
--   Gallai Edmonds: comps eq of mem
-- statement:
--   The Gallai Edmonds construction uses the comps eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L116-L118
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L116-L118

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

theorem GallaiEdmonds.comps_eq_of_mem {K K' : Set V} (hK : K ∈ comps G W) (hK' : K' ∈ comps G W)
    (hy : y ∈ K) (hy' : y ∈ K') : K = K' := by sorry
