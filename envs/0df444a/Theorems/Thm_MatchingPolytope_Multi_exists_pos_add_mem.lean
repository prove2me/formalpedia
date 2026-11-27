-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_exists_pos_add_mem
-- name    : MatchingPolytope.Multi.exists_pos_add_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:45.81715+00:00
-- url     : https://prove2.me/theorems/b870454d-511c-56fb-ae9a-60b1541e602e
-- title:
--   Multi: exists pos add mem
-- statement:
--   From an irreducible point one can move a little in any kernel direction.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L118-L170
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L118-L170

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.exists_pos_add_mem [DecidableEq V] (hV : Valid ends W F) {y d : E → ℝ}
    (hy : y ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F y) (hd : Ker ends W F d) :
    ∃ ε : ℝ, 0 < ε ∧ y + ε • d ∈ Poly ends W F := by sorry
