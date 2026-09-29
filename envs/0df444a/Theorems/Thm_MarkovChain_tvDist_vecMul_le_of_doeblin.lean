-- Prove2me | Theorems.Thm_MarkovChain_tvDist_vecMul_le_of_doeblin
-- name    : MarkovChain.tvDist_vecMul_le_of_doeblin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:06:11.777177+00:00
-- url     : https://prove2.me/theorems/9fbd4eb9-ff79-4d02-be8c-17138c1f07fa
-- title:
--   Doeblin minorization makes the transition operator a contraction
-- statement:
--   **The contraction estimate.** If the chain satisfies Doeblin's condition $M_{ij} \ge \varepsilon\,\nu_j$, then one step contracts total variation by the factor $1-\varepsilon$:
--   $$d_{\mathrm{TV}}(\mu M, \mu' M) \le (1-\varepsilon)\, d_{\mathrm{TV}}(\mu, \mu')$$
--   for all distributions $\mu, \mu'$. This single inequality is the engine of the whole convergence theory: uniqueness of the stationary distribution, the geometric rate, and convergence from an arbitrary start are all corollaries.
--
--   The proof is three lines of exact algebra. Write $d = \mu - \mu'$, so $\sum_i d_i = 0$, and set $Q_{ij} = M_{ij} - \varepsilon\nu_j \ge 0$, a nonnegative matrix with constant row sums $1 - \varepsilon$. Because $d$ has total mass zero the subtracted rank-one part is invisible to it:
--   $$(\mu M)_j - (\mu' M)_j = \sum_i d_i M_{ij} = \sum_i d_i Q_{ij}.$$
--   Now the triangle inequality and nonnegativity of $Q$ give
--   $$\sum_j\Big|\sum_i d_i Q_{ij}\Big| \le \sum_i |d_i| \sum_j Q_{ij} = (1-\varepsilon)\sum_i |d_i|.$$
--   Nothing is lost anywhere except in the one triangle inequality, and no coupling, no spectral theory and no positivity of $\varepsilon$ are used — for $\varepsilon = 0$ the estimate degenerates to the (true, and separately useful) statement that stochastic matrices are non-expansive in total variation.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem tvDist_vecMul_le_of_doeblin {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ μ' : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hμ' : μ' ∈ stdSimplex ℝ n) :
    tvDist (μ ᵥ* M) (μ' ᵥ* M) ≤ (1 - ε) * tvDist μ μ' := by
  sorry

end MarkovChain
