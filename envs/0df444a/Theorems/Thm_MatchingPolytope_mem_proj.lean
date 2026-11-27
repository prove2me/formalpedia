-- Prove2me | Theorems.Thm_MatchingPolytope_mem_proj
-- name    : MatchingPolytope.mem_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:43.765414+00:00
-- url     : https://prove2.me/theorems/b1a7a207-0fef-481b-a80f-bbe4149abeec
-- title:
--   Matching Polytope: mem proj
-- statement:
--   The Matching Polytope construction uses the mem proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L342-L344
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L342-L344

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.mem_proj {N : Finset (DEdge G)} {e : G.edgeSet} : e ∈ proj G N ↔ Sum.inl e ∈ N := by sorry
