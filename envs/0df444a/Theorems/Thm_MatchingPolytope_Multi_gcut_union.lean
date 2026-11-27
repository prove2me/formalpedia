-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_union
-- name    : MatchingPolytope.Multi.gcut_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:50.776573+00:00
-- url     : https://prove2.me/theorems/6adb8250-15c6-51ab-8519-01b9fe3488b9
-- title:
--   Multi: gcut union
-- statement:
--   The Multi construction uses the gcut union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L100-L104
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L100-L104

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.gcut_union [DecidableEq E] (M N : Finset E) (T : Finset V) :
    gcut ends (M ∪ N) T = gcut ends M T ∪ gcut ends N T := by sorry
