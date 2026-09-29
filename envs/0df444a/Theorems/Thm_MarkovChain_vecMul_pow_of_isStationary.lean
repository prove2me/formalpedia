-- Prove2me | Theorems.Thm_MarkovChain_vecMul_pow_of_isStationary
-- name    : MarkovChain.vecMul_pow_of_isStationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:12:07.599137+00:00
-- url     : https://prove2.me/theorems/7d329743-c2f6-4b65-90cf-9cc8accca876
-- title:
--   A stationary distribution is fixed by every power of the chain
-- statement:
--   If $\pi M = \pi$ then $\pi M^k = \pi$ for every $k$: equilibrium is preserved by running the chain for any number of steps. An immediate induction, using $M^{k+1} = M^k M$ and `vecMul_vecMul`. It is the statement that lets the $k$-step convergence estimate compare $\mu M^k$ with $\pi$ rather than with a moving target.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem vecMul_pow_of_isStationary {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {π : n → ℝ}
    (hπ : IsStationary M π) (k : ℕ) : π ᵥ* M ^ k = π := by
  sorry

end MarkovChain
