-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_filter_collapse_other
-- name    : MatchingPolytope.Multi.filter_collapse_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:48.491817+00:00
-- url     : https://prove2.me/theorems/8bd58db0-9ec6-51aa-a896-019a32c27c70
-- title:
--   Multi: filter collapse other
-- statement:
--   The Multi construction uses the filter collapse other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L142-L153
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L142-L153

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

theorem MatchingPolytope.Multi.filter_collapse_other {R : Finset V} {r : V} (hr : r ∈ R) {v : V} (hv : v ∈ W)
    (hvR : v ∉ R) : W.filter (fun u => collapse R r u ∈ ({v} : Finset V)) = {v} := by sorry
