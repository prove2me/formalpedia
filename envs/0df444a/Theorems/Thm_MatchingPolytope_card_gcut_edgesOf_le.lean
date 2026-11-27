-- Prove2me | Theorems.Thm_MatchingPolytope_card_gcut_edgesOf_le
-- name    : MatchingPolytope.card_gcut_edgesOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:32.5181+00:00
-- url     : https://prove2.me/theorems/c9bbd101-559f-5c1e-b2b6-6f3fce0d3c1d
-- title:
--   Matching Polytope: card gcut edges Of le
-- statement:
--   The Matching Polytope construction uses the card gcut edges Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L107-L119
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L107-L119

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.card_gcut_edgesOf_le {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (gcut (edgeEnds G) (edgesOf G M) {v}).card ≤ 1 := by sorry
