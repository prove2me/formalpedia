-- Prove2me | Theorems.Thm_GallaiEdmonds_exists_max_missing
-- name    : GallaiEdmonds.exists_max_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:03:30.752082+00:00
-- url     : https://prove2.me/theorems/e7b2804a-1b8a-4622-985d-c42994ddb7f1
-- title:
--   Gallai Edmonds: exists max missing
-- statement:
--   For a minimal barrier `U`, every vertex in an odd component of `G − U` is missed by some
--   maximum matching.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L213-L237
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L213-L237

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.exists_max_missing [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧
      (∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M'.edgeSet.ncard) ∧ v ∉ M'.verts := by sorry
