-- Prove2me | Theorems.Thm_GallaiEdmonds_perfectMatching_C
-- name    : GallaiEdmonds.perfectMatching_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:06.958185+00:00
-- url     : https://prove2.me/theorems/213ea0ee-81cf-41b6-a899-0c0d009c105b
-- title:
--   Gallai Edmonds: perfect Matching C
-- statement:
--   `G[C(G)]` has a perfect matching.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L163-L173
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L163-L173

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

theorem GallaiEdmonds.perfectMatching_C [Finite V] : HasPerfectMatchingOn G (setC G) := by sorry
