-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gw_right
-- name    : MatchingPolytope.Multi.gw_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:43.207805+00:00
-- url     : https://prove2.me/theorems/31f317b3-052d-503c-ba01-66d829cdfe90
-- title:
--   Multi: gw right
-- statement:
--   The Multi construction uses the gw right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L91-L96
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L91-L96

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.gw_right [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ g ∈ C, ∑ M, w1 M * chi M g = x g)
    (h2' : ∀ N, w2 N ≠ 0 → ∑ g ∈ C, chi N g = 1) (ψ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * ψ p.2 = ∑ N, w2 N * ψ N := by sorry
