-- Prove2me | Theorems.Thm_GallaiEdmonds_oddC_le_ncard
-- name    : GallaiEdmonds.oddC_le_ncard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:20.580877+00:00
-- url     : https://prove2.me/theorems/49f86d1a-979b-540f-94cd-fe03b6f5e51f
-- title:
--   Gallai Edmonds: odd C le ncard
-- statement:
--   The Gallai Edmonds construction uses the odd C le ncard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L64-L67
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L64-L67

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

theorem GallaiEdmonds.oddC_le_ncard [Finite V] (H : SimpleGraph V) (W : Set V) : oddC H W ≤ W.ncard := by sorry
