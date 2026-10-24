-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_eq_G22
-- name    : OfflineCMC.Minimax.eq_G22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:57.028883+00:00
-- url     : https://prove2.me/theorems/b740550e-cd57-42f2-b563-ba86a37ccfc0
-- title:
--   (G.22), p. 51 — chain rule bound KL(P_σ ‖ P_0) ≤ p★·m·D_σ for the path laws of M_σ and M_0
-- statement:
--   Let $d\ge2$ be even, $0<p_\star<1/(d+1)$, $0<\varepsilon<1/32$ and $\sigma\in\{-1,1\}^{d/2}$. Let $P_\sigma$ and $P_0$ be the laws of the path $(X_0,\dots,X_m)$ of the Markov chains with initial law $b$ and transition matrices $M_\sigma$ (G.19) and $M_0$ (all rows $b$). Let $D_\sigma=D(\eta(\sigma)\|b)$. Then
--   $$
--   D_{\sigma,m}:=D(P_\sigma\,\|\,P_0)\le p_\star\,m\,D_\sigma .
--   $$
--
--   The divergence between the path laws grows linearly in $m$, at the rate $p_\star D_\sigma$: only visits to the special state, which occur with probability $p_\star$, carry information about $\sigma$. This is the input to the information-theoretic lower bound.
--
--   **Formalization Note** The path laws are the explicit product mass functions on sequences $(x_0,\dots,x_m)$.
--
--   Differences from the source:
--   - reading: "the KL-divergence between $M_0$ and $M_\sigma$ … viewed as distributions over sequences of length $m$" → $D(P_\sigma\|P_0)$ for the path $(X_0,\dots,X_m)$; reason: this direction matches $D_\sigma=D(\eta(\sigma)\|b)$, and the paper's sample is $(X_0,\dots,X_m)$
--   - reading: no initial law given → initial law $b$ for both chains; reason: the page fixes none; $b$ is the law every row shares in its last column, so $P_\sigma(X_i=d+1)=p_\star$ for every $i$
--   - generalization: $\sigma\in\Sigma$ and $d>2$ → every $\sigma\in\{-1,1\}^{d/2}$ and every even $d\ge2$; reason: covers the source's cases
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 51, eq. (G.22), App. G.3 Part 1 (citing Wolfer–Kontorovich [68, Lemma 6.2])

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_HardFamily

namespace OfflineCMC.Minimax

theorem eq_G22 (d : ℕ) (hd : Even d) (hd0 : 0 < d) (p ε : ℝ) (hp : 0 < p)
    (hpd : p < 1 / ((d : ℝ) + 1)) (hε : 0 < ε) (hε' : ε < 1 / 32) (σ : Fin (d / 2) → ℤˣ)
    (m : ℕ) :
    klDivFin (pathLaw (baseRow d p) (hardMatrix d p ε σ) m)
        (pathLaw (baseRow d p) (baseMatrix d p) m) ≤
      p * (m : ℝ) * klDivFin (etaRow d p ε σ) (baseRow d p) := by sorry

end OfflineCMC.Minimax
