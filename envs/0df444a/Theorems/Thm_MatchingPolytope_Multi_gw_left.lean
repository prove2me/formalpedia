-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gw_left
-- name    : MatchingPolytope.Multi.gw_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:32.907224+00:00
-- url     : https://prove2.me/theorems/dc468861-2cba-4d5b-8f83-6c1260adb78e
-- title:
--   Multi: gw left
-- statement:
--   The Multi construction uses the gw left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L59-L81
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L59-L81

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.gw_left [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h2 : ∀ g ∈ C, ∑ N, w2 N * chi N g = x g)
    (h1' : ∀ M, w1 M ≠ 0 → ∑ g ∈ C, chi M g = 1) (φ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * φ p.1 = ∑ M, w1 M * φ M := by sorry
