-- Prove2me | Theorems.Thm_MatchingPolytope_inside_eq_innerEdges
-- name    : MatchingPolytope.inside_eq_innerEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:30:51.46162+00:00
-- url     : https://prove2.me/theorems/d2e38b5b-d888-54ce-8421-741f62a06243
-- title:
--   Matching Polytope: inside eq inner Edges
-- statement:
--   The Matching Polytope construction uses the inside eq inner Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L43-L45
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L43-L45

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.inside_eq_innerEdges (S : Finset V) : inside (edgeEnds G) univ S = innerEdges G S := by sorry
