-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_shrinkF_of_subset
-- name    : MatchingPolytope.Multi.shrinkF_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:01.815417+00:00
-- url     : https://prove2.me/theorems/a42d547c-1a21-4caf-9909-e330a09750e9
-- title:
--   Multi: shrink F of subset
-- statement:
--   The Multi construction uses the shrink F of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L43-L47
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L43-L47

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

theorem MatchingPolytope.Multi.shrinkF_of_subset {R : Finset V} {M : Finset E} (hM : M ⊆ shrinkF ends F R) :
    shrinkF ends M R = M := by sorry
