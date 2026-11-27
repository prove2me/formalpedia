-- Prove2me | Theorems.Thm_MatchingPolytope_sum_gcut_dEnds
-- name    : MatchingPolytope.sum_gcut_dEnds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:22.056397+00:00
-- url     : https://prove2.me/theorems/847060ab-b8fb-4720-b5de-9befd2327014
-- title:
--   Matching Polytope: sum gcut d Ends
-- statement:
--   The Matching Polytope construction uses the sum gcut d Ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L198-L239
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L198-L239

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.sum_gcut_dEnds (z : DEdge G → ℝ) (T : Finset (V ⊕ V)) :
    ∑ e ∈ gcut (dEnds G) univ T, z e =
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inl v ∈ T), z (Sum.inl e) +
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inr v ∈ T), z (Sum.inr (Sum.inl e)) +
      ∑ v ∈ univ.filter (fun v => ¬ (Sum.inl v ∈ T ↔ Sum.inr v ∈ T)),
        z (Sum.inr (Sum.inr v)) := by sorry
