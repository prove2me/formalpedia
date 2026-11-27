-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_shrink_valid
-- name    : MatchingPolytope.Multi.shrink_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:20.423424+00:00
-- url     : https://prove2.me/theorems/73901255-641c-5790-abed-d240f0caead9
-- title:
--   Multi: shrink valid
-- statement:
--   The Multi construction uses the shrink valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L69-L92
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L69-L92

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

theorem MatchingPolytope.Multi.shrink_valid (hV : Valid ends W F) {R : Finset V} {r : V} (hr : r ∈ R) :
    Valid (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by sorry
