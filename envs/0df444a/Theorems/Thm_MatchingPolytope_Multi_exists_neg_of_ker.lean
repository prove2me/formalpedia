-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_exists_neg_of_ker
-- name    : MatchingPolytope.Multi.exists_neg_of_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:03.388037+00:00
-- url     : https://prove2.me/theorems/708dada4-d860-4743-9522-718876bb4f85
-- title:
--   Multi: exists neg of ker
-- statement:
--   The Multi construction uses the exists neg of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L172-L183
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L172-L183

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.exists_neg_of_ker (hV : Valid ends W F) {d : E → ℝ} (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ e, d e < 0 := by sorry
