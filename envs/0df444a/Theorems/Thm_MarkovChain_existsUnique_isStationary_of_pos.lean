-- Prove2me | Theorems.Thm_MarkovChain_existsUnique_isStationary_of_pos
-- name    : MarkovChain.existsUnique_isStationary_of_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:33:59.340051+00:00
-- url     : https://prove2.me/theorems/e4fa66a3-50b7-4605-907f-973a5179d484
-- title:
--   A positive transition matrix has a unique stationary distribution
-- statement:
--   **Capstone.** A row-stochastic matrix whose entries are all bounded below by a positive constant has exactly one stationary distribution. Existence is the unconditional Cesàro/compactness theorem; uniqueness follows because positivity supplies Doeblin's condition (with the uniform measure and $\varepsilon = |S|c$), and a Doeblin chain has at most one equilibrium. Together with the convergence theorem this is the finite-state Perron–Frobenius statement in probabilistic form: a strictly positive chain has a unique equilibrium and converges to it geometrically from every initial condition.
-- source:
--   J. R. Norris, Markov Chains, Cambridge University Press 1997, Chapter 1 (SS1.7 invariant distributions, SS1.8 convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem existsUnique_isStationary_of_pos {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {c : ℝ} (hne : Nonempty n)
    (hM : M ∈ rowStochastic ℝ n) (hc : 0 < c) (h : ∀ i j, c ≤ M i j) :
    ∃! π : n → ℝ, IsStationary M π := by
  sorry

end MarkovChain
