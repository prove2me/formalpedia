-- Prove2me | Theorems.Thm_MatchingPolytope_isPerfectMatching_subgraphOf
-- name    : MatchingPolytope.isPerfectMatching_subgraphOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:28:49.169796+00:00
-- url     : https://prove2.me/theorems/4a0e8974-a32b-4a5d-9d67-a062e519811f
-- title:
--   Matching Polytope: is Perfect Matching subgraph Of
-- statement:
--   The Matching Polytope construction uses the is Perfect Matching subgraph Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L148-L166
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L148-L166

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.isPerfectMatching_subgraphOf {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : (subgraphOf G M).IsPerfectMatching := by sorry
