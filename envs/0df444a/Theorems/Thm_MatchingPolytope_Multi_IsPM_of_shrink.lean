-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_IsPM_of_shrink
-- name    : MatchingPolytope.Multi.IsPM.of_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:59.761716+00:00
-- url     : https://prove2.me/theorems/04924fd4-9de2-41a6-ae9b-9a724b61591f
-- title:
--   Is PM: of shrink
-- statement:
--   A perfect matching of the shrunk multigraph, seen in the original multigraph.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L233-L246
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L233-L246

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

theorem MatchingPolytope.Multi.IsPM.of_shrink (hV : Valid ends W F) {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R)
    {M : Finset E} (hM : IsPM (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) M) :
    M ⊆ shrinkF ends F R ∧ (gcut ends M R).card = 1 ∧
      ∀ v ∈ W, v ∉ R → (gcut ends M {v}).card = 1 := by sorry
