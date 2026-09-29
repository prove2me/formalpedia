-- Prove2me | Theorems.Thm_MarkovChain_tvDist_le_one
-- name    : MarkovChain.tvDist_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:03:34.546985+00:00
-- url     : https://prove2.me/theorems/e337aa95-d7c3-4c86-9adc-c82d07cb9578
-- title:
--   Total variation distance between distributions is at most one
-- statement:
--   Between two probability vectors the total variation distance never exceeds $1$: $|\mu_i - \nu_i| \le \mu_i + \nu_i$ pointwise by nonnegativity, so $\sum_i |\mu_i - \nu_i| \le 2$. Together with the metric axioms this says the simplex has total-variation diameter at most $1$, which is what turns the geometric contraction estimate into a bound uniform over all starting distributions.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem tvDist_le_one {n : Type*} [Fintype n] [DecidableEq n] {μ ν : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n)
    (hν : ν ∈ stdSimplex ℝ n) :
    tvDist μ ν ≤ 1 := by
  sorry

end MarkovChain
