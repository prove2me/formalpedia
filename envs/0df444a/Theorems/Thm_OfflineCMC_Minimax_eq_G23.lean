-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_eq_G23
-- name    : OfflineCMC.Minimax.eq_G23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:13.056474+00:00
-- url     : https://prove2.me/theorems/f9ee4559-eb61-41f7-94ac-58f4481d19f7
-- title:
--   (G.23), p. 53 — the vector (G.23) is the stationary distribution of M_σ
-- statement:
--   Let $d\ge2$ be even, $0<p_\star<1/(d+1)$, $0<\varepsilon<1/32$ and $\sigma\in\{-1,1\}^{d/2}$. Let $\pi_\sigma$ be the vector
--   $$
--   \pi_\sigma=\Big(\frac{(1-p_\star)^2+(1-p_\star+16\sigma_1\varepsilon)p_\star}{d},\dots,\frac{(1-p_\star)^2+(1-p_\star-16\sigma_{d/2}\varepsilon)p_\star}{d},\ p_\star\Big). \tag{G.23}
--   $$
--   Then $\pi_\sigma$ is the stationary distribution of the transition matrix $M_\sigma$ of (G.19):
--
--   1. $\pi_\sigma$ is a probability vector and $\pi_\sigma M_\sigma=\pi_\sigma$;
--   2. every probability vector $\pi$ with $\pi M_\sigma=\pi$ equals $\pi_\sigma$.
--
--   With Kac's formula, the stationary probabilities give the expected return times of the hard chain. This relates $p_\star$ and $d$ to the return-time constant $T$ of Assumption 2.
--
--   Differences from the source:
--   - reading: "represents the stationary distribution" → $\pi_\sigma$ is a stationary probability vector and the only one; reason: "the" stationary distribution asserts uniqueness
--   - generalization: $d>2$ even → $d\ge2$ even; reason: covers $d=2$ as well
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 53, eq. (G.23), App. G.3 Part 1

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_HardFamily

namespace OfflineCMC.Minimax

theorem eq_G23 (d : ℕ) (hd : Even d) (hd0 : 0 < d) (p ε : ℝ) (hp : 0 < p)
    (hpd : p < 1 / ((d : ℝ) + 1)) (hε : 0 < ε) (hε' : ε < 1 / 32) (σ : Fin (d / 2) → ℤˣ) :
    (∀ t, 0 ≤ statDist d p ε σ t) ∧ ∑ t, statDist d p ε σ t = 1 ∧
      (∀ t, ∑ s, statDist d p ε σ s * hardMatrix d p ε σ s t = statDist d p ε σ t) ∧
      ∀ π : Fin (d + 1) → ℝ, (∀ t, 0 ≤ π t) → ∑ t, π t = 1 →
        (∀ t, ∑ s, π s * hardMatrix d p ε σ s t = π t) → π = statDist d p ε σ := by sorry

end OfflineCMC.Minimax
