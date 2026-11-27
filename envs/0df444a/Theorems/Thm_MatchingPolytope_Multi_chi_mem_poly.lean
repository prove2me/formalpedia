-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_chi_mem_poly
-- name    : MatchingPolytope.Multi.chi_mem_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:39.736117+00:00
-- url     : https://prove2.me/theorems/f5f5c137-cd0e-5816-af99-5a845bbce22e
-- title:
--   Multi: chi mem poly
-- statement:
--   The Multi construction uses the chi mem poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L250-L258
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L250-L258

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

theorem MatchingPolytope.Multi.chi_mem_poly (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) :
    chi M ∈ Poly ends W F := by sorry
