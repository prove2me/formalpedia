-- Prove2me | Theorems.Thm_MatchingPolytope_edmonds_matching_polytope
-- name    : MatchingPolytope.edmonds_matching_polytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:31:35.987859+00:00
-- url     : https://prove2.me/theorems/96fd49cf-3018-4f9e-9fcc-2169ad23fadc
-- title:
--   Matching Polytope: edmonds matching polytope
-- statement:
--   **Edmonds' matching polytope theorem**: the convex hull of the incidence vectors of the
--   matchings of a finite simple graph is described by nonnegativity, the degree inequalities and
--   the odd-set inequalities.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L367-L390
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean#L367-L390

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MatchingPolytope.edmonds_matching_polytope :
    convexHull ℝ (matchingVectors G) = matchingPolytope G := by sorry
