-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
-- name    : MatchingPolytope.Multi.Valid.pair_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:31.406802+00:00
-- url     : https://prove2.me/theorems/2d2fd20b-8019-5a9e-a7e2-bcafc032a2f9
-- title:
--   Valid: pair of mem
-- statement:
--   The Valid construction uses the pair of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L101-L107
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L101-L107

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

theorem MatchingPolytope.Multi.Valid.pair_of_mem (hV : Valid ends W F) {e : E} (he : e ∈ F) {v : V} (hv : v ∈ ends e) :
    ∃ b, b ≠ v ∧ b ∈ W ∧ ends e = s(v, b) := by sorry
