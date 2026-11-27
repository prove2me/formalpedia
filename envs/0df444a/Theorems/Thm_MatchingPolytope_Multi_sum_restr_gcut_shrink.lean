-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_sum_restr_gcut_shrink
-- name    : MatchingPolytope.Multi.sum_restr_gcut_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:01.011696+00:00
-- url     : https://prove2.me/theorems/9caef747-2a11-465d-bd54-f6e259dc1f9b
-- title:
--   Multi: sum restr gcut shrink
-- statement:
--   The Multi construction uses the sum restr gcut shrink property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L205-L212
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L205-L212

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

theorem MatchingPolytope.Multi.sum_restr_gcut_shrink (hV : Valid ends W F) (R : Finset V) (r : V) (T : Finset V)
    (x : E → ℝ) :
    ∑ e ∈ gcut (shrinkEnds ends R r) (shrinkF ends F R) T, restr (shrinkF ends F R) x e =
      ∑ e ∈ gcut ends F (W.filter fun u => collapse R r u ∈ T), x e := by sorry
