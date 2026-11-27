-- Prove2me | Theorems.Thm_MatchingPolytope_gcut_eq_cutEdges
-- name    : MatchingPolytope.gcut_eq_cutEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:54.407707+00:00
-- url     : https://prove2.me/theorems/8068659e-73c9-4130-bc2b-48d70d119e44
-- title:
--   Matching Polytope: gcut eq cut Edges
-- statement:
--   The Matching Polytope construction uses the gcut eq cut Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L92-L95
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L92-L95

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

theorem MatchingPolytope.gcut_eq_cutEdges [DecidableEq V] (S : Finset V) :
    gcut (edgeEnds G) univ S = cutEdges G S := by sorry
