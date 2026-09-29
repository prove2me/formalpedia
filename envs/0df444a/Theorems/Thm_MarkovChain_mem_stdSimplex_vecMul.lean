-- Prove2me | Theorems.Thm_MarkovChain_mem_stdSimplex_vecMul
-- name    : MarkovChain.mem_stdSimplex_vecMul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T18:58:32.215397+00:00
-- url     : https://prove2.me/theorems/fd746a88-086c-4322-8d20-bcfe2e509ad0
-- title:
--   The transition operator maps distributions to distributions
-- statement:
--   If $M$ is row-stochastic and $\mu$ is a probability vector, then so is $\mu M$: the chain maps distributions to distributions. Nonnegativity is immediate; the total mass is preserved because
--   $$\sum_j (\mu M)_j = \sum_j \sum_i \mu_i M_{ij} = \sum_i \mu_i \sum_j M_{ij} = \sum_i \mu_i = 1,$$
--   exchanging the two finite sums and using that each row of $M$ sums to $1$. This is the well-definedness statement that every later result rests on; iterating it (with `pow_mem`) shows that $\mu M^k$ is a distribution for every $k$.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem mem_stdSimplex_vecMul {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    {μ : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) :
    μ ᵥ* M ∈ stdSimplex ℝ n := by
  sorry

end MarkovChain
