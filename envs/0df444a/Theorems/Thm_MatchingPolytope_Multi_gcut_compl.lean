-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_compl
-- name    : MatchingPolytope.Multi.gcut_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:46.161211+00:00
-- url     : https://prove2.me/theorems/3d4d92d8-bc8b-5622-a479-14ba433ad5db
-- title:
--   Multi: gcut compl
-- statement:
--   The Multi construction uses the gcut compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L140-L155
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L140-L155

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.gcut_compl [DecidableEq V] (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (S : Finset V) :
    gcut ends D (W \ S) = gcut ends D S := by sorry
