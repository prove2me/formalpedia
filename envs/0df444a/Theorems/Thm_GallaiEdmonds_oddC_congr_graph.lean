-- Prove2me | Theorems.Thm_GallaiEdmonds_oddC_congr_graph
-- name    : GallaiEdmonds.oddC_congr_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:27.806262+00:00
-- url     : https://prove2.me/theorems/015ee76c-7fa2-5476-9d04-d1b0e496db47
-- title:
--   Gallai Edmonds: odd C congr graph
-- statement:
--   The Gallai Edmonds construction uses the odd C congr graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L69-L74
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L69-L74

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

theorem GallaiEdmonds.oddC_congr_graph {H : SimpleGraph V} {W : Set V}
    (h : ∀ a ∈ W, ∀ b ∈ W, H.Adj a b ↔ G.Adj a b) : oddC H W = oddC G W := by sorry
