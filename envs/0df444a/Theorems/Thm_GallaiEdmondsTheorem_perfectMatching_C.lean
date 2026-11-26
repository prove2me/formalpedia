-- Prove2me | Theorems.Thm_GallaiEdmondsTheorem_perfectMatching_C
-- name    : GallaiEdmondsTheorem.perfectMatching_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:38.687562+00:00
-- url     : https://prove2.me/theorems/71261a04-6fd6-42d6-ae7c-05d2ec27a281
-- title:
--   Gallai Edmonds Theorem: perfect Matching C
-- statement:
--   `G[C(G)]` has a perfect matching.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L82-L83
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L82-L83

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_perfectMatching_C

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmondsTheorem.perfectMatching_C [Finite V] : HasPerfectMatchingOn G (setC G) := by sorry
