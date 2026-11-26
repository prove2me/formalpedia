-- Prove2me | Theorems.Thm_GallaiEdmonds_factorCritical
-- name    : GallaiEdmonds.factorCritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:34.318902+00:00
-- url     : https://prove2.me/theorems/246e3275-b196-5889-ab8d-84f211526b6c
-- title:
--   Gallai Edmonds: factor Critical
-- statement:
--   Every connected component of `G[D(G)]` is factor-critical.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L147-L160
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L147-L160

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmonds.factorCritical [Finite V] (c : (G.induce (setD G)).ConnectedComponent) :
    ∀ v ∈ compSet G c, HasPerfectMatchingOn G (compSet G c \ {v}) := by sorry
