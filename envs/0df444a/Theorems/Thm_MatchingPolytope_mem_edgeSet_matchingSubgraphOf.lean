-- Prove2me | Theorems.Thm_MatchingPolytope_mem_edgeSet_matchingSubgraphOf
-- name    : MatchingPolytope.mem_edgeSet_matchingSubgraphOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:24.872183+00:00
-- url     : https://prove2.me/theorems/ad145e80-bf7c-5d77-a885-6f9740bfd29f
-- title:
--   Matching Polytope: mem edge Set matching Subgraph Of
-- statement:
--   The Matching Polytope construction uses the mem edge Set matching Subgraph Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L67-L76
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L67-L76

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

theorem MatchingPolytope.mem_edgeSet_matchingSubgraphOf {M : Finset G.edgeSet} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (matchingSubgraphOf G M).edgeSet ↔ e ∈ M := by sorry
