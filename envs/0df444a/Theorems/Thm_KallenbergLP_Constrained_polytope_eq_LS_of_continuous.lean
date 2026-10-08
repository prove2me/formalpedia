-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_polytope_eq_LS_of_continuous
-- name    : KallenbergLP.Constrained.polytope_eq_LS_of_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:59.059743+00:00
-- url     : https://prove2.me/theorems/26d03201-2f95-481d-a32c-ae8c44befac1
-- title:
--   Theorem 4.7.9 — if x(π) is continuous in π, then X = L(S)
-- statement:
--   Let $\beta$ be an initial distribution. For a stationary decision rule $\pi$ put $x_{ja}(\pi)=[\beta^TP^*(\pi)]_j\pi_{ja}$. If the map $\pi\mapsto x(\pi)$, from the set of stationary decision rules (a product of simplices, with the product topology) to frequency vectors, is continuous, then
--
--   $$X=L(S),$$
--
--   that is, every point of the polytope (4.7.8) is the frequency limit of some stationary policy.
--
--   Under this condition the constrained problem always has a stationary optimal policy.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 155, Theorem 4.7.9

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.9, p. 155: if `x(π)` of (4.7.2) is continuous in the stationary
decision rule `π` (product topology on the product of simplices), then `X = L(S)`. -/
theorem polytope_eq_LS_of_continuous {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1)
    (hcont : Continuous (fun π : StatRule M => xStat β (π : KallenbergLP.AverageLP.Pair M → ℝ))) :
    polytopeX M β = Lset M β IsStationary := by sorry

end KallenbergLP.Constrained
