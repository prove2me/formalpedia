-- Prove2me | Theorems.Thm_MatchingPolytope_convex_matchingPolytope
-- name    : MatchingPolytope.convex_matchingPolytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:01.593212+00:00
-- url     : https://prove2.me/theorems/e593582d-5089-4621-b5dc-2c63727ebdde
-- title:
--   Matching Polytope: convex matching Polytope
-- statement:
--   The Matching Polytope construction uses the convex matching Polytope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L146-L167
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L146-L167

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.convex_matchingPolytope : Convex ℝ (matchingPolytope G) := by sorry
