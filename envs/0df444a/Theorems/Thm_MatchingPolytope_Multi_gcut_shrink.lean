-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_shrink
-- name    : MatchingPolytope.Multi.gcut_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:51.39203+00:00
-- url     : https://prove2.me/theorems/40e9066b-8637-4337-ba94-7ab52d74ea83
-- title:
--   Multi: gcut shrink
-- statement:
--   The cut of `T` in the shrunk multigraph is the cut of the preimage of `T`.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L103-L127
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L103-L127

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

theorem MatchingPolytope.Multi.gcut_shrink (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (R : Finset V) (r : V)
    (T : Finset V) :
    gcut (shrinkEnds ends R r) (shrinkF ends D R) T =
      gcut ends D (W.filter fun u => collapse R r u ∈ T) := by sorry
