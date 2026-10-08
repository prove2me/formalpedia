-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_polytope_eq_LS_unichain
-- name    : KallenbergLP.Constrained.polytope_eq_LS_unichain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:16.208034+00:00
-- url     : https://prove2.me/theorems/ab62e528-4bf3-4345-841a-641fdada9eb9
-- title:
--   Theorem 4.7.10 — in the unichain case X = L(S)
-- statement:
--   Assume (Assumption 4.7.1) that for every pure stationary policy $f^\infty$ the Markov chain with transition matrix $P(f)$ has one ergodic set plus a (perhaps empty) set of transient states. Then for every initial distribution $\beta$,
--
--   $$X=L(S):$$
--
--   every point of the polytope (4.7.8) is the unique frequency limit $x(\pi)$ of some stationary policy $\pi^\infty$.
--
--   Consequently, in the unichain case the constrained average-reward problem always has a stationary optimal policy, which can be computed from one linear program.
--
--   **Formalization Note** Assumption 4.7.1 is the platform predicate `IsUnichain M`.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 158, Assumption 4.7.1; p. 159, Theorem 4.7.10

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.10, p. 159, under Assumption 4.7.1 (p. 158): if for every pure
stationary `f^∞` the chain under `P(f)` has one ergodic set plus a (perhaps empty) set of
transient states, then `X = L(S)`. -/
theorem polytope_eq_LS_unichain {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M) (β : S → ℝ)
    (hβ0 : ∀ j, 0 ≤ β j) (hβ1 : ∑ j, β j = 1) :
    polytopeX M β = Lset M β IsStationary := by sorry

end KallenbergLP.Constrained
