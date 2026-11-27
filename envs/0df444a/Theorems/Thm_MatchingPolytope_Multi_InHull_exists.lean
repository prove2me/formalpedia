-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_InHull_exists
-- name    : MatchingPolytope.Multi.InHull.exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:05.458254+00:00
-- url     : https://prove2.me/theorems/0b3c0f1c-2f35-5161-a17c-5cac3a7991fa
-- title:
--   In Hull: exists
-- statement:
--   The In Hull construction uses the exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L317-L321
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L317-L321

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

theorem MatchingPolytope.Multi.InHull.exists {Q : Finset E → Prop} {x : E → ℝ} (h : InHull Q x) : ∃ M, Q M := by sorry
