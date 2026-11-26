-- Prove2me | Theorems.Thm_GallaiEdmonds_partner_eq
-- name    : GallaiEdmonds.partner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:00.435894+00:00
-- url     : https://prove2.me/theorems/87c3ae39-7422-4405-9fc0-7bc489229681
-- title:
--   Gallai Edmonds: partner eq
-- statement:
--   The Gallai Edmonds construction uses the partner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L60-L62
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L60-L62

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

theorem GallaiEdmonds.partner_eq {M : G.Subgraph} (hM : M.IsMatching) {y w : V} (h : M.Adj y w) :
    partner hM y = w := by sorry
