-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_restr_mem_poly_shrink
-- name    : MatchingPolytope.Multi.restr_mem_poly_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:28.454959+00:00
-- url     : https://prove2.me/theorems/d227e1fa-5c9b-592e-bb4e-5a20888a4238
-- title:
--   Multi: restr mem poly shrink
-- statement:
--   The restriction of `x` to the shrunk multigraph lies in its polytope.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L215-L230
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L215-L230

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

theorem MatchingPolytope.Multi.restr_mem_poly_shrink (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R) (hRodd : Odd R.card)
    (htight : ∑ e ∈ gcut ends F R, x e = 1) :
    restr (shrinkF ends F R) x ∈ Poly (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by sorry
