-- Prove2me | Theorems.Thm_MatchingPolytope_dvec_mem_poly
-- name    : MatchingPolytope.dvec_mem_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:21.060502+00:00
-- url     : https://prove2.me/theorems/e4eeef5b-78e2-40bb-ba9e-4d116c22c410
-- title:
--   Matching Polytope: dvec mem poly
-- statement:
--   The Matching Polytope construction uses the dvec mem poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L285-L336
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L285-L336

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.dvec_mem_poly {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) :
    dvec G x ∈ Multi.Poly (dEnds G) univ univ := by sorry
