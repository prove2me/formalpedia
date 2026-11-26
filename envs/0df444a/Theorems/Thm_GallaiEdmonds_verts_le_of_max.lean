-- Prove2me | Theorems.Thm_GallaiEdmonds_verts_le_of_max
-- name    : GallaiEdmonds.verts_le_of_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:30.897816+00:00
-- url     : https://prove2.me/theorems/cc67656c-ed01-565f-b59d-51dacece0c43
-- title:
--   Gallai Edmonds: verts le of max
-- statement:
--   The Gallai Edmonds construction uses the verts le of max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L40-L45
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L40-L45

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.verts_le_of_max [Finite V] {M M' : G.Subgraph} (hM' : M'.IsMatching) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M'.verts.ncard ≤ M.verts.ncard := by sorry
