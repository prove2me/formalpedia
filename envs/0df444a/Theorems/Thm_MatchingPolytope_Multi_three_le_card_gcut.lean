-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_three_le_card_gcut
-- name    : MatchingPolytope.Multi.three_le_card_gcut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:21.394794+00:00
-- url     : https://prove2.me/theorems/85709d16-6def-4e98-8218-f71e5c868e3a
-- title:
--   Multi: three le card gcut
-- statement:
--   In an irreducible point of a multigraph with at least five vertices, every vertex has
--   degree at least three.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L357-L416
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L357-L416

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.three_le_card_gcut [DecidableEq V] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hW5 : 5 ≤ W.card) {v : V} (hv : v ∈ W) :
    3 ≤ (gcut ends F {v}).card := by sorry
