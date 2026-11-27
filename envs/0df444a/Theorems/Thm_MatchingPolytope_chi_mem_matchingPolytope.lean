-- Prove2me | Theorems.Thm_MatchingPolytope_chi_mem_matchingPolytope
-- name    : MatchingPolytope.chi_mem_matchingPolytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:45.132288+00:00
-- url     : https://prove2.me/theorems/ffb8d06d-7896-52ae-8376-4a160b194b2e
-- title:
--   Matching Polytope: chi mem matching Polytope
-- statement:
--   The Matching Polytope construction uses the chi mem matching Polytope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L127-L144
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L127-L144

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.chi_mem_matchingPolytope {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingPolytope G := by sorry
