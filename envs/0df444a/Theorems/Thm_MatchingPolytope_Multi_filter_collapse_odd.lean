-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_filter_collapse_odd
-- name    : MatchingPolytope.Multi.filter_collapse_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:54.361663+00:00
-- url     : https://prove2.me/theorems/d1e0ec5d-0823-598f-8cd9-3307a551cfc7
-- title:
--   Multi: filter collapse odd
-- statement:
--   The Multi construction uses the filter collapse odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L155-L203
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L155-L203

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.filter_collapse_odd {R : Finset V} {r : V} (hr : r ∈ R) (hRW : R ⊆ W)
    (hRodd : Odd R.card) {T : Finset V} (hT : T ⊆ shrinkW W R r) (hTodd : Odd T.card) :
    Odd (W.filter fun u => collapse R r u ∈ T).card := by sorry
