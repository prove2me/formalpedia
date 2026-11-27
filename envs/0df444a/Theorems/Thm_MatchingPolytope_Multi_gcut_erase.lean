-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_erase
-- name    : MatchingPolytope.Multi.gcut_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:14.372847+00:00
-- url     : https://prove2.me/theorems/83b3ca03-b8f2-5340-aa64-69bbeefe9eff
-- title:
--   Multi: gcut erase
-- statement:
--   The Multi construction uses the gcut erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L54-L59
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L54-L59

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.gcut_erase [DecidableEq E] (e : E) (T : Finset V) :
    gcut ends (F.erase e) T = (gcut ends F T).erase e := by sorry
