-- Prove2me | Theorems.Thm_MatchingPolytope_isPM_edgesOf
-- name    : MatchingPolytope.isPM_edgesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:28:04.697623+00:00
-- url     : https://prove2.me/theorems/cb1c8bd6-c601-44ee-8a84-46fbcc01b1c3
-- title:
--   Matching Polytope: is PM edges Of
-- statement:
--   The Matching Polytope construction uses the is PM edges Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L125-L146
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L125-L146

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

theorem MatchingPolytope.isPM_edgesOf {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    IsPM (edgeEnds G) univ univ (edgesOf G M) := by sorry
