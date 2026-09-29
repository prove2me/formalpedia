-- Prove2me | Theorems.Thm_MarkovChain_tvDist_metric
-- name    : MarkovChain.tvDist_metric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:00:17.433001+00:00
-- url     : https://prove2.me/theorems/2c81d0f1-687e-483b-8484-289c406e1a75
-- title:
--   Total variation distance is a metric
-- statement:
--   The total variation distance $d(\mu,\nu) = \tfrac12\sum_i|\mu_i - \nu_i|$ is a genuine metric on vectors indexed by the state space: it is nonnegative, symmetric, vanishes exactly when the two vectors coincide, and satisfies the triangle inequality. Stated as a single conjunction because these are the four properties any later argument uses interchangeably; separating them into four theorems would only fragment the interface. Note that nothing here requires the arguments to be distributions — that hypothesis enters only in the bound $d \le 1$.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem tvDist_metric {n : Type*} [Fintype n] [DecidableEq n] (μ ν ρ : n → ℝ) :
    0 ≤ tvDist μ ν ∧ tvDist μ ν = tvDist ν μ ∧ (tvDist μ ν = 0 ↔ μ = ν) ∧
      tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  sorry

end MarkovChain
