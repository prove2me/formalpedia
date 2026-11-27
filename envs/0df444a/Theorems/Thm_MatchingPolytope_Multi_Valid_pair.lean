-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_Valid_pair
-- name    : MatchingPolytope.Multi.Valid.pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:54.127519+00:00
-- url     : https://prove2.me/theorems/005b947d-530b-5c45-bfc9-757000dc4f6f
-- title:
--   Valid: pair
-- statement:
--   The Valid construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L91-L96
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L91-L96

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

theorem MatchingPolytope.Multi.Valid.pair (hV : Valid ends W F) {e : E} (he : e ∈ F) :
    ∃ a b, a ≠ b ∧ a ∈ W ∧ b ∈ W ∧ ends e = s(a, b) := by sorry
