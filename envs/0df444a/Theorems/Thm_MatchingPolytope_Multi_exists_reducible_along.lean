-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_exists_reducible_along
-- name    : MatchingPolytope.Multi.exists_reducible_along
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:51.375128+00:00
-- url     : https://prove2.me/theorems/1b395203-a71c-5090-acc4-46e7f4376f93
-- title:
--   Multi: exists reducible along
-- statement:
--   Moving from an irreducible point along a nonzero kernel direction reaches a reducible
--   point.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L187-L216
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L187-L216

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.exists_reducible_along [DecidableEq V] (hV : Valid ends W F) {x d : E → ℝ}
    (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ Poly ends W F ∧ Reducible ends W F (x + t • d) := by sorry
