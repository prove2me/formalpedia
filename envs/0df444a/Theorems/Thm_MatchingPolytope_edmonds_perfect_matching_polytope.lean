-- Prove2me | Theorems.Thm_MatchingPolytope_edmonds_perfect_matching_polytope
-- name    : MatchingPolytope.edmonds_perfect_matching_polytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:30:12.826212+00:00
-- url     : https://prove2.me/theorems/dd08b18e-c7cf-5234-ac6b-a1d61cea284e
-- title:
--   Matching Polytope: edmonds perfect matching polytope
-- statement:
--   **Edmonds' perfect matching polytope theorem** (Edmonds 1965): the convex hull of the
--   incidence vectors of the perfect matchings of a finite simple graph is described by
--   nonnegativity, the degree equations and the odd-set inequalities.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L180-L198
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L180-L198

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi

theorem MatchingPolytope.edmonds_perfect_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G := by sorry
