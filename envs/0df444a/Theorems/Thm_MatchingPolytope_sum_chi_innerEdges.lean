-- Prove2me | Theorems.Thm_MatchingPolytope_sum_chi_innerEdges
-- name    : MatchingPolytope.sum_chi_innerEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:43.976257+00:00
-- url     : https://prove2.me/theorems/2b84b6d8-de37-56b7-b96d-2f930613b91a
-- title:
--   Matching Polytope: sum chi inner Edges
-- statement:
--   The Matching Polytope construction uses the sum chi inner Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L123-L125
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L123-L125

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.sum_chi_innerEdges (M : Finset G.edgeSet) (S : Finset V) :
    ∑ e ∈ innerEdges G S, chi M e = ((inside (edgeEnds G) M S).card : ℝ) := by sorry
