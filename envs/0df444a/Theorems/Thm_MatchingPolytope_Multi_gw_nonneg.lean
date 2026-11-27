-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gw_nonneg
-- name    : MatchingPolytope.Multi.gw_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:44.460797+00:00
-- url     : https://prove2.me/theorems/3eb1701c-74f6-4097-a8f7-99ead67876a7
-- title:
--   Multi: gw nonneg
-- statement:
--   The Multi construction uses the gw nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L39-L50
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L39-L50

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.gw_nonneg {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, 0 < x g) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ M, 0 ≤ w1 M) (h2 : ∀ M, 0 ≤ w2 M) (p : Finset E × Finset E) :
    0 ≤ gw C x w1 w2 p := by sorry
