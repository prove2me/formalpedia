-- Prove2me | Theorems.Thm_MatchingPolytope_lower_bound
-- name    : MatchingPolytope.lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:01.416731+00:00
-- url     : https://prove2.me/theorems/71669cbd-4a27-513d-88f6-7959ef581860
-- title:
--   Matching Polytope: lower bound
-- statement:
--   The Matching Polytope construction uses the lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L245-L283
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L245-L283

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.lower_bound {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) (A B : Finset V)
    (hodd : Odd (A \ B).card) :
    1 ≤ ∑ e ∈ cutEdges G A, x e + ∑ e ∈ cutEdges G B, x e +
      ∑ v ∈ univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)), (1 - ∑ e ∈ cutEdges G {v}, x e) := by sorry
