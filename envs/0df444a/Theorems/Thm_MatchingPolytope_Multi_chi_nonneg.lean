-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_chi_nonneg
-- name    : MatchingPolytope.Multi.chi_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:52.450801+00:00
-- url     : https://prove2.me/theorems/644f1b4e-446a-4569-9a0d-67a58671a198
-- title:
--   Multi: chi nonneg
-- statement:
--   The Multi construction uses the chi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L31-L32
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L31-L32

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.chi_nonneg (M : Finset E) (e : E) : 0 ≤ chi M e := by sorry
