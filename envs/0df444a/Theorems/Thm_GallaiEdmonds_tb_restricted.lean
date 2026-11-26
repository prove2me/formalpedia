-- Prove2me | Theorems.Thm_GallaiEdmonds_tb_restricted
-- name    : GallaiEdmonds.tb_restricted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:31.858466+00:00
-- url     : https://prove2.me/theorems/9bc39ce0-7e82-49b6-bba1-359095f80cc5
-- title:
--   Gallai Edmonds: tb restricted
-- statement:
--   Tutte–Berge restricted to a vertex set `S` (the `≥` half of the formula).
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L94-L124
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L94-L124

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

theorem GallaiEdmonds.tb_restricted [Finite V] (G : SimpleGraph V) (S : Set V) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts ⊆ S ∧ ∃ T ⊆ S,
      S.ncard + T.ncard ≤ N.verts.ncard + oddC G (S \ T) := by sorry
