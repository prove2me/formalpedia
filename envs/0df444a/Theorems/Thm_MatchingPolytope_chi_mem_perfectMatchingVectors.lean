-- Prove2me | Theorems.Thm_MatchingPolytope_chi_mem_perfectMatchingVectors
-- name    : MatchingPolytope.chi_mem_perfectMatchingVectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:28:32.735457+00:00
-- url     : https://prove2.me/theorems/4134c58b-4ffc-43e0-97d7-108a6fdfa007
-- title:
--   Matching Polytope: chi mem perfect Matching Vectors
-- statement:
--   The Matching Polytope construction uses the chi mem perfect Matching Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L168-L173
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L168-L173

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

theorem MatchingPolytope.chi_mem_perfectMatchingVectors {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : chi M ∈ perfectMatchingVectors G := by sorry
