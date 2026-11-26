-- Prove2me | Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
-- name    : GallaiEdmonds.mem_cc_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:18.984801+00:00
-- url     : https://prove2.me/theorems/55f39d67-9f7c-4eaa-a535-54503f5685bd
-- title:
--   Gallai Edmonds: mem cc of adj
-- statement:
--   The Gallai Edmonds construction uses the mem cc of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L67-L69
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L67-L69

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

theorem GallaiEdmonds.mem_cc_of_adj (h : y ∈ cc G W x) (hz : z ∈ W) (hadj : G.Adj y z) : z ∈ cc G W x := by sorry
