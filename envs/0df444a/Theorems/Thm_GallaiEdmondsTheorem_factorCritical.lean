-- Prove2me | Theorems.Thm_GallaiEdmondsTheorem_factorCritical
-- name    : GallaiEdmondsTheorem.factorCritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:10.376809+00:00
-- url     : https://prove2.me/theorems/a2afcf68-84dc-5516-bc59-7b43ffc30714
-- title:
--   Gallai Edmonds Theorem: factor Critical
-- statement:
--   Every connected component of `G[D(G)]` is factor-critical.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L77-L79
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L77-L79

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_factorCritical

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmondsTheorem.factorCritical [Finite V] (c : (G.induce (setD G)).ConnectedComponent) :
    ∀ v ∈ compSet G c, HasPerfectMatchingOn G (compSet G c \ {v}) := by sorry
