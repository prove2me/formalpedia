-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inside_subset
-- name    : MatchingPolytope.Multi.inside_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:07.714412+00:00
-- url     : https://prove2.me/theorems/55c2aadf-525c-4590-aebd-531b4c430e6f
-- title:
--   Multi: inside subset
-- statement:
--   The Multi construction uses the inside subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L134-L135
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L134-L135

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.inside_subset (D : Finset E) (S : Finset V) : inside ends D S ⊆ D := by sorry
