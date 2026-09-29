-- Prove2me | Theorems.Thm_MarkovChain_tendsto_vecMul_pow_of_doeblin
-- name    : MarkovChain.tendsto_vecMul_pow_of_doeblin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:17:51.20798+00:00
-- url     : https://prove2.me/theorems/729d5960-9eb5-4fb7-8ab0-a812b8026dbe
-- title:
--   Convergence to equilibrium
-- statement:
--   **The convergence theorem.** For a chain satisfying Doeblin's condition, the distribution after $k$ steps converges to the stationary distribution from *any* starting distribution: both in total variation, $d_{\mathrm{TV}}(\mu M^k, \pi) \to 0$, and coordinatewise, $(\mu M^k)_i \to \pi_i$ for every state $i$. The chain forgets its initial condition.
--
--   The first conclusion squeezes the geometric estimate between $0$ and $(1-\varepsilon)^k\,d_{\mathrm{TV}}(\mu,\pi) \to 0$, using $0 \le 1-\varepsilon < 1$, which is exactly where both $\varepsilon > 0$ and $\varepsilon \le 1$ are needed. The second follows from the first because a single coordinate difference is at most twice the total variation distance, so $(\mu M^k)_i - \pi_i$ is squeezed between $\pm 2\,d_{\mathrm{TV}}(\mu M^k, \pi)$.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem tendsto_vecMul_pow_of_doeblin {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ π : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hπ : IsStationary M π) :
    Tendsto (fun k => tvDist (μ ᵥ* M ^ k) π) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => (μ ᵥ* M ^ k) i) atTop (𝓝 (π i)) := by
  sorry

end MarkovChain
