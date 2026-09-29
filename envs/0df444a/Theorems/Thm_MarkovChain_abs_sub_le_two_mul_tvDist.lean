-- Prove2me | Theorems.Thm_MarkovChain_abs_sub_le_two_mul_tvDist
-- name    : MarkovChain.abs_sub_le_two_mul_tvDist
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:02:35.400968+00:00
-- url     : https://prove2.me/theorems/5dbe7884-9ee4-48c2-b428-bfb5bde18f38
-- title:
--   Total variation controls every coordinate
-- statement:
--   Each coordinate difference is controlled by the total variation distance: $|\mu_i - \nu_i| \le 2\,d_{\mathrm{TV}}(\mu,\nu)$ for every state $i$, since a single summand is at most the whole sum of absolute values. This is the bridge from convergence in total variation to pointwise convergence of the distributions, and it is what makes the convergence theorem's second conclusion follow from its first.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem abs_sub_le_two_mul_tvDist {n : Type*} [Fintype n] [DecidableEq n] (μ ν : n → ℝ) (i : n) :
    |μ i - ν i| ≤ 2 * tvDist μ ν := by
  sorry

end MarkovChain
