-- Prove2me | Theorems.Thm_MatchingPolytope_mem_edgesOf
-- name    : MatchingPolytope.mem_edgesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:34.779879+00:00
-- url     : https://prove2.me/theorems/745747aa-1839-5293-8eb6-688f83ad7314
-- title:
--   Matching Polytope: mem edges Of
-- statement:
--   The Matching Polytope construction uses the mem edges Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L115-L118
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L115-L118

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

theorem MatchingPolytope.mem_edgesOf {M : G.Subgraph} {e : G.edgeSet} :
    e ∈ edgesOf G M ↔ (e : Sym2 V) ∈ M.edgeSet := by sorry
