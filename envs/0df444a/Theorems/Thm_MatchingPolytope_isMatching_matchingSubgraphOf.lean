-- Prove2me | Theorems.Thm_MatchingPolytope_isMatching_matchingSubgraphOf
-- name    : MatchingPolytope.isMatching_matchingSubgraphOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:29.195594+00:00
-- url     : https://prove2.me/theorems/c32e5c29-2829-5bd5-9882-d5c75258967d
-- title:
--   Matching Polytope: is Matching matching Subgraph Of
-- statement:
--   The Matching Polytope construction uses the is Matching matching Subgraph Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L78-L92
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L78-L92

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} (G : SimpleGraph V)

theorem MatchingPolytope.isMatching_matchingSubgraphOf {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : (matchingSubgraphOf G M).IsMatching := by sorry
