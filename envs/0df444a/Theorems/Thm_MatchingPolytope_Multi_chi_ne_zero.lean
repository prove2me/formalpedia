-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_chi_ne_zero
-- name    : MatchingPolytope.Multi.chi_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:53.579902+00:00
-- url     : https://prove2.me/theorems/af8d11e7-fde8-47fe-bfc1-5eff306ccd38
-- title:
--   Multi: chi ne zero
-- statement:
--   The Multi construction uses the chi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L34-L37
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L34-L37

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.chi_ne_zero {M : Finset E} {e : E} (h : chi M e ≠ 0) : e ∈ M := by sorry
