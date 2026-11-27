-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gw_ne_zero
-- name    : MatchingPolytope.Multi.gw_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:42.685495+00:00
-- url     : https://prove2.me/theorems/07c41e9a-16e2-5633-95e0-50f522896931
-- title:
--   Multi: gw ne zero
-- statement:
--   The Multi construction uses the gw ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L52-L57
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L52-L57

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.gw_ne_zero {C : Finset E} {x : E → ℝ} {w1 w2 : Finset E → ℝ} {p : Finset E × Finset E}
    (h : gw C x w1 w2 p ≠ 0) :
    ∃ g ∈ C, g ∈ p.1 ∧ g ∈ p.2 ∧ w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 := by sorry
