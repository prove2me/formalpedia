-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_shrinkEnds_pair
-- name    : MatchingPolytope.Multi.shrinkEnds_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:46.305064+00:00
-- url     : https://prove2.me/theorems/7a93df19-7a0e-47dd-a44b-56c6b0e9d474
-- title:
--   Multi: shrink Ends pair
-- statement:
--   The Multi construction uses the shrink Ends pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L65-L67
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L65-L67

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

theorem MatchingPolytope.Multi.shrinkEnds_pair {R : Finset V} {r : V} {e : E} {a b : V} (h : ends e = s(a, b)) :
    shrinkEnds ends R r e = s(collapse R r a, collapse R r b) := by sorry
