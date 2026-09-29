-- Prove2me | Theorems.Thm_MarkovChain_isStationary_unif_of_colSum
-- name    : MarkovChain.isStationary_unif_of_colSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:29:55.350546+00:00
-- url     : https://prove2.me/theorems/1fc862fc-0bff-4103-b837-0b5070d82e67
-- title:
--   A doubly stochastic chain is stationary at the uniform distribution
-- statement:
--   If in addition to the row sums the *column* sums of the transition matrix are $1$ — that is, if the matrix is doubly stochastic — then the uniform distribution is stationary:
--   $$(\mathrm{unif}\,M)_j = \sum_i |S|^{-1} M_{ij} = |S|^{-1}\sum_i M_{ij} = |S|^{-1}.$$
--   Only the column condition is used, so the hypothesis is stated as such rather than through Mathlib's `colStochastic`. This covers random walks on regular graphs, and every chain whose transition matrix is symmetric or a convex combination of permutation matrices.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem isStationary_unif_of_colSum {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hne : Nonempty n)
    (hcol : ∀ j, ∑ i, M i j = 1) : IsStationary M (unif n) := by
  sorry

end MarkovChain
