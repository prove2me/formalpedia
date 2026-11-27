-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gw_swap
-- name    : MatchingPolytope.Multi.gw_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:55.607639+00:00
-- url     : https://prove2.me/theorems/b012e9bc-7fb1-421e-b82f-f0bbf9666e29
-- title:
--   Multi: gw swap
-- statement:
--   The Multi construction uses the gw swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L83-L89
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L83-L89

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.gw_swap (C : Finset E) (x : E → ℝ) (w1 w2 : Finset E → ℝ) (p : Finset E × Finset E) :
    gw C x w1 w2 p = gw C x w2 w1 p.swap := by sorry
