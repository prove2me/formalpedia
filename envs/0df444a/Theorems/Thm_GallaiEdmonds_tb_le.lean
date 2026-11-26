-- Prove2me | Theorems.Thm_GallaiEdmonds_tb_le
-- name    : GallaiEdmonds.tb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:42.436861+00:00
-- url     : https://prove2.me/theorems/1c48beff-38dc-583b-a745-8a6925a97a21
-- title:
--   Gallai Edmonds: tb le
-- statement:
--   Tutte–Berge inequality.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L77-L80
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L77-L80

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

theorem GallaiEdmonds.tb_le [Finite V] {M : G.Subgraph} (hM : M.IsMatching) (U : Set V) :
    M.verts.ncard + oddC G Uᶜ ≤ Nat.card V + U.ncard := by sorry
