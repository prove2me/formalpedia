-- Prove2me | Theorems.Thm_MatchingPolytope_chi_mem_matchingVectors
-- name    : MatchingPolytope.chi_mem_matchingVectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:36.484784+00:00
-- url     : https://prove2.me/theorems/d4a03ec1-b7d3-50ef-b2e2-18e809543f99
-- title:
--   Matching Polytope: chi mem matching Vectors
-- statement:
--   The Matching Polytope construction uses the chi mem matching Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L94-L99
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L94-L99

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} (G : SimpleGraph V)

theorem MatchingPolytope.chi_mem_matchingVectors {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingVectors G := by sorry
