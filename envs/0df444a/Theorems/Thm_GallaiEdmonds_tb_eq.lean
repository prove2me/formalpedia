-- Prove2me | Theorems.Thm_GallaiEdmonds_tb_eq
-- name    : GallaiEdmonds.tb_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:33.665647+00:00
-- url     : https://prove2.me/theorems/abab2fd5-5fe6-43c5-87af-6e386f702fb0
-- title:
--   Gallai Edmonds: tb eq
-- statement:
--   Tutte–Berge formula: a maximum matching and a set attaining equality.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L83-L91
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L83-L91

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

theorem GallaiEdmonds.tb_eq [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by sorry
