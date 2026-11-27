-- Prove2me | Theorems.Thm_MatchingPolytope_incidence_eq_chi
-- name    : MatchingPolytope.incidence_eq_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:28:02.417568+00:00
-- url     : https://prove2.me/theorems/b56c3c79-acac-46f4-9b8d-f4ad1160a89d
-- title:
--   Matching Polytope: incidence eq chi
-- statement:
--   The Matching Polytope construction uses the incidence eq chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L120-L123
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L120-L123

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

theorem MatchingPolytope.incidence_eq_chi (M : G.Subgraph) : incidence G M = chi (edgesOf G M) := by sorry
