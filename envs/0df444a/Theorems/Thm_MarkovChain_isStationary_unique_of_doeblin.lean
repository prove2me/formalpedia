-- Prove2me | Theorems.Thm_MarkovChain_isStationary_unique_of_doeblin
-- name    : MarkovChain.isStationary_unique_of_doeblin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:09:21.196985+00:00
-- url     : https://prove2.me/theorems/22ed0f40-27cd-41dd-a1fe-71ba1d3e1ea6
-- title:
--   A Doeblin chain has at most one stationary distribution
-- statement:
--   Under Doeblin's condition with $\varepsilon > 0$ the stationary distribution is unique. If $\pi$ and $\pi'$ are both stationary then applying the contraction estimate to them and rewriting $\pi M = \pi$, $\pi' M = \pi'$ gives
--   $$d_{\mathrm{TV}}(\pi,\pi') \le (1-\varepsilon)\,d_{\mathrm{TV}}(\pi,\pi'),$$
--   so $\varepsilon\, d_{\mathrm{TV}}(\pi,\pi') \le 0$; since $\varepsilon > 0$ and the distance is nonnegative it must vanish, and a total variation distance vanishes only between equal vectors. Combined with the unconditional existence theorem this gives existence *and* uniqueness for every Doeblin chain.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem isStationary_unique_of_doeblin {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {π π' : n → ℝ} (h1 : IsStationary M π) (h2 : IsStationary M π') : π = π' := by
  sorry

end MarkovChain
