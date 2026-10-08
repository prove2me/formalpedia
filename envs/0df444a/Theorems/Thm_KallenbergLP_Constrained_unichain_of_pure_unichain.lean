-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_unichain_of_pure_unichain
-- name    : KallenbergLP.Constrained.unichain_of_pure_unichain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:57.416698+00:00
-- url     : https://prove2.me/theorems/e517a7d4-757c-4b8e-ba02-8220b12f6162
-- title:
--   Lemma 4.6.1 — at most one ergodic set under every pure policy implies the same under every stationary policy
-- statement:
--   Consider a finite Markov decision model with stochastic transitions. If for every pure stationary policy $f^\infty$ the Markov chain with transition matrix $P(f)$, $P(f)_{ij}=p_{if(i)j}$, has at most one ergodic set, then for every stationary policy $\pi^\infty$ the Markov chain with transition matrix
--
--   $$P(\pi)_{ij}=\sum_{a\in A(i)}p_{iaj}\,\pi_{ia}$$
--
--   also has at most one ergodic set.
--
--   The lemma lets a unichain assumption stated for the finitely many pure policies be used for all randomized stationary policies.
--
--   **Formalization Note** An ergodic set is a closed communicating class. "At most one ergodic set" is the platform predicate `IsUnichainMatrix` (any two recurrent states are mutually accessible), and the hypothesis is the platform's `IsUnichain M`. For a finite chain, which always has an ergodic set, "at most one" and "exactly one plus transient states" coincide.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 129, Lemma 4.6.1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Lemma 4.6.1, p. 129: if the Markov chain induced by `P(f)` has at most one
ergodic set for every pure stationary `f^∞`, then the Markov chain induced by `P(π)` has at most
one ergodic set for every stationary `π^∞`. -/
theorem unichain_of_pure_unichain {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) :
    IsUnichainMatrix (policyMatrix π) := by sorry

end KallenbergLP.Constrained
