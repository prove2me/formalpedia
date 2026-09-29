-- Prove2me | Theorems.Thm_MarkovChain_tvDist_vecMul_pow_le
-- name    : MarkovChain.tvDist_vecMul_pow_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:14:30.878479+00:00
-- url     : https://prove2.me/theorems/4af8f787-17a6-46df-a4a8-d954c4d7365d
-- title:
--   Geometric convergence rate under Doeblin's condition
-- statement:
--   Iterating the contraction estimate gives an explicit geometric rate: for a Doeblin chain, every starting distribution $\mu$ and every stationary $\pi$,
--   $$d_{\mathrm{TV}}(\mu M^k, \pi) \le (1-\varepsilon)^k\, d_{\mathrm{TV}}(\mu, \pi).$$
--   The induction needs three ingredients: that $\mu M^k$ is again a distribution (so the contraction estimate applies to it), that $\pi M = \pi$ so the target does not move, and that $1 - \varepsilon \ge 0$ so the inductive bound may be multiplied through. Together with $d_{\mathrm{TV}} \le 1$ on distributions this yields the mixing bound $d_{\mathrm{TV}}(\mu M^k, \pi) \le (1-\varepsilon)^k$ uniformly in $\mu$ — in particular the chain mixes to within $\delta$ in $O(\varepsilon^{-1}\log \delta^{-1})$ steps.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem tvDist_vecMul_pow_le {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ π : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hπ : IsStationary M π) (k : ℕ) :
    tvDist (μ ᵥ* M ^ k) π ≤ (1 - ε) ^ k * tvDist μ π := by
  sorry

end MarkovChain
