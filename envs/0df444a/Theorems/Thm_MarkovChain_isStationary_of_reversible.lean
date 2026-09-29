-- Prove2me | Theorems.Thm_MarkovChain_isStationary_of_reversible
-- name    : MarkovChain.isStationary_of_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:25:25.896024+00:00
-- url     : https://prove2.me/theorems/fae03668-1bb7-47e5-b442-e5dedacc5f81
-- title:
--   Detailed balance implies stationarity
-- statement:
--   If a probability vector $\pi$ satisfies detailed balance, $\pi_i M_{ij} = \pi_j M_{ji}$ for all states, then it is stationary. The computation is one line:
--   $$(\pi M)_j = \sum_i \pi_i M_{ij} = \sum_i \pi_j M_{ji} = \pi_j \sum_i M_{ji} = \pi_j,$$
--   using detailed balance termwise and then that row $j$ of $M$ sums to $1$. The converse is false, which is exactly why the reversible case is singled out: detailed balance is a local, checkable condition that exhibits the stationary distribution without solving the global linear system $\pi M = \pi$. It is how the stationary distribution of a random walk on a weighted graph, or of a Metropolis chain, is identified in practice.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem isStationary_of_reversible {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    {π : n → ℝ} (hπ : π ∈ stdSimplex ℝ n) (hrev : IsReversible M π) :
    IsStationary M π := by
  sorry

end MarkovChain
