-- Prove2me | Theorems.Thm_GallaiEdmonds_two_mul_card_add
-- name    : GallaiEdmonds.two_mul_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:51.70468+00:00
-- url     : https://prove2.me/theorems/3e9a3153-2298-4b3c-929f-dbdb8ec18331
-- title:
--   Gallai Edmonds: two mul card add
-- statement:
--   **The Gallai–Edmonds formula.** For every maximum matching `M`,
--   `2|M| + c(D(G)) = |V| + |A(G)|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L208-L215
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L208-L215

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

theorem GallaiEdmonds.two_mul_card_add [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    2 * M.edgeSet.ncard + Nat.card (G.induce (setD G)).ConnectedComponent =
      Nat.card V + (setA G).ncard := by sorry
