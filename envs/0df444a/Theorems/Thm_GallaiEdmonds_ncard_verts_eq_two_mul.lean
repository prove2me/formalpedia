-- Prove2me | Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul
-- name    : GallaiEdmonds.ncard_verts_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:06.034908+00:00
-- url     : https://prove2.me/theorems/e010c61e-b4c9-4bd5-8bdd-9aac3d22f5a7
-- title:
--   Gallai Edmonds: ncard verts eq two mul
-- statement:
--   The Gallai Edmonds construction uses the ncard verts eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L29-L45
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L29-L45

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
open Finset

theorem GallaiEdmonds.ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by sorry
