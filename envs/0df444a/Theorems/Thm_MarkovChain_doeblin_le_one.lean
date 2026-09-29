-- Prove2me | Theorems.Thm_MarkovChain_doeblin_le_one
-- name    : MarkovChain.doeblin_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:04:57.886777+00:00
-- url     : https://prove2.me/theorems/d11a5b27-6526-4594-b219-b12aadc9c51b
-- title:
--   A Doeblin constant is at most one
-- statement:
--   If $M$ is row-stochastic and satisfies Doeblin's condition $M_{ij} \ge \varepsilon\,\nu_j$ with $\nu$ a distribution, then $\varepsilon \le 1$. Indeed, summing the minorization over $j$ in any single row gives $\varepsilon = \varepsilon\sum_j \nu_j \le \sum_j M_{ij} = 1$; the existence of a state to sum over comes from $\nu$ being a distribution, which already forces the state space to be nonempty. Small, but it is what makes the contraction factor $1-\varepsilon$ nonnegative, and therefore what lets the geometric convergence estimate be iterated.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem doeblin_le_one {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν) : ε ≤ 1 := by
  sorry

end MarkovChain
