-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset
-- name    : MatchingPolytope.Multi.shrinkF_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:26.349533+00:00
-- url     : https://prove2.me/theorems/2b834677-8cf7-51a8-966d-41556dfd0f78
-- title:
--   Multi: shrink F subset
-- statement:
--   The Multi construction uses the shrink F subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L41-L41
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L41-L41

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {F : Finset E}

theorem MatchingPolytope.Multi.shrinkF_subset (R : Finset V) : shrinkF ends F R ⊆ F := by sorry
