-- Prove2me | Theorems.Thm_GallaiEdmonds_partner_adj
-- name    : GallaiEdmonds.partner_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:20.395491+00:00
-- url     : https://prove2.me/theorems/865c4970-8970-5e2a-9a34-576ace4572ba
-- title:
--   Gallai Edmonds: partner adj
-- statement:
--   The Gallai Edmonds construction uses the partner adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L56-L58
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L56-L58

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.partner_adj {M : G.Subgraph} (hM : M.IsMatching) {y : V} (hy : y ∈ M.verts) :
    M.Adj y (partner hM y) := by sorry
