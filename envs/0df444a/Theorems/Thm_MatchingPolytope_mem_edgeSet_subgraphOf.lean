-- Prove2me | Theorems.Thm_MatchingPolytope_mem_edgeSet_subgraphOf
-- name    : MatchingPolytope.mem_edgeSet_subgraphOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:50.654872+00:00
-- url     : https://prove2.me/theorems/8e7dd764-263c-41f6-879e-66e1ea196a31
-- title:
--   Matching Polytope: mem edge Set subgraph Of
-- statement:
--   The Matching Polytope construction uses the mem edge Set subgraph Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L69-L78
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L69-L78

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} (G : SimpleGraph V)

theorem MatchingPolytope.mem_edgeSet_subgraphOf {M : Finset G.edgeSet} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (subgraphOf G M).edgeSet ↔ e ∈ M := by sorry
