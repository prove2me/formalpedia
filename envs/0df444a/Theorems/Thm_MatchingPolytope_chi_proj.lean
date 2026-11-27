-- Prove2me | Theorems.Thm_MatchingPolytope_chi_proj
-- name    : MatchingPolytope.chi_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:08.024826+00:00
-- url     : https://prove2.me/theorems/f49ecbf5-699a-54e0-b81d-601a20cc95be
-- title:
--   Matching Polytope: chi proj
-- statement:
--   The Matching Polytope construction uses the chi proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L346-L348
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L346-L348

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.chi_proj (N : Finset (DEdge G)) (e : G.edgeSet) : chi (proj G N) e = chi N (Sum.inl e) := by sorry
