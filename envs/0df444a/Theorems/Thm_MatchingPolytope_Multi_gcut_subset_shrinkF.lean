-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_subset_shrinkF
-- name    : MatchingPolytope.Multi.gcut_subset_shrinkF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:58.097657+00:00
-- url     : https://prove2.me/theorems/67ffd5c4-b182-5b9c-8895-9bd35d88ffaa
-- title:
--   Multi: gcut subset shrink F
-- statement:
--   The Multi construction uses the gcut subset shrink F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L106-L111
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L106-L111

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.gcut_subset_shrinkF {S R : Finset V} (h : ∀ u, u ∉ S → u ∉ R) :
    gcut ends F S ⊆ shrinkF ends F R := by sorry
