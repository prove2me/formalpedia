-- Prove2me | Theorems.Thm_MatchingPolytope_card_gcut_proj_le
-- name    : MatchingPolytope.card_gcut_proj_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:43.341392+00:00
-- url     : https://prove2.me/theorems/b342c816-5174-4e6c-a107-0f86b435a777
-- title:
--   Matching Polytope: card gcut proj le
-- statement:
--   The Matching Polytope construction uses the card gcut proj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L350-L362
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L350-L362

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.card_gcut_proj_le {N : Finset (DEdge G)} (hN : IsPM (dEnds G) univ univ N) (v : V) :
    (gcut (edgeEnds G) (proj G N) {v}).card ≤ 1 := by sorry
