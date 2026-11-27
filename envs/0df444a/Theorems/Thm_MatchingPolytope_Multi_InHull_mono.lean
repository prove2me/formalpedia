-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_InHull_mono
-- name    : MatchingPolytope.Multi.InHull.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:40.852+00:00
-- url     : https://prove2.me/theorems/1abfaf04-5368-4d27-9f88-f966387e82f4
-- title:
--   In Hull: mono
-- statement:
--   The In Hull construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L275-L278
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L275-L278

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
variable [Fintype E]

theorem MatchingPolytope.Multi.InHull.mono {Q Q' : Finset E → Prop} (hQ : ∀ M, Q M → Q' M) {x : E → ℝ}
    (h : InHull Q x) : InHull Q' x := by sorry
