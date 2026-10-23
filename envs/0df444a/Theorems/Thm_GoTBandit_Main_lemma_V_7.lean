-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_V_7
-- name    : GoTBandit.Main.lemma_V_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:36.812466+00:00
-- url     : https://prove2.me/theorems/e36757ef-9eda-4568-911e-e84284476396
-- title:
--   Lemma V.7, Eq. (31), p. 10 — Markov concentration of the visits to z* during one GoT phase
-- statement:
--   There is a universal constant $B_0$ with the following property. Let $N\le M$, $M\ge2$, $c_2\ge1$, $\delta>0$ and $0<\eta<1$. Then for all sufficiently large $k$: for positive utilities $U$ with a unique optimal profile $a^*$, every $0<\varepsilon<1$ and $c>0$, every stationary distribution $\pi$ of the GoT chain $P^\varepsilon$, and every initial law $\phi$ on $Z$ that vanishes where $\pi$ does, a run of the chain of $L=\lceil c_2k^\delta\rceil$ turns started from $\phi$ satisfies
--
--   $$
--   P_g=\mathbb P\Big(\sum_{t=1}^{L}I(z(t)=z^*)\le(1-\eta)\pi_{z^*}\lceil c_2k^\delta\rceil\Big)\le B_0\|\phi\|_\pi\,e^{-\frac{\eta^2\pi_{z^*}c_2k^\delta}{72T_m(1/8)}},
--   $$
--
--   where $z^*=[a^*,C^N]$, $\|\phi\|_\pi=\sqrt{\sum_z\phi_z^2/\pi_z}$ and $T_m(1/8)$ is the mixing time of $P^\varepsilon$ with accuracy $1/8$.
--
--   This is the per-phase concentration of the number of visits to the optimal state; it feeds the Chernoff argument of Lemma V.8.
--
--   **Formalization Note** $B_0$ is chosen before everything else (independent of $\eta$, $\pi_{z^*}$ and the chain, as in the cited Markov-chain Chernoff bound), and the threshold on $k$ depends only on $N,M,c_2,\delta,\eta$. The paper's $\phi_k$, the law of the state at the start of the GoT phase, is generalized to every initial law. The hypothesis that $\phi$ vanishes where $\pi$ does is added: the chain has transient states with $\pi=0$, where $\|\phi\|_\pi$ is $+\infty$ on paper but Lean's $x/0=0$ would make it small. $T_m(1/8)$ is the worst-start total-variation mixing time `MarkovMixing.mixingTime P π (1/8)`. The page labels $B_0\|\phi_k\|_\pi$ as $A_k$; that label is omitted. Here $\eta$ is the slack parameter, not the collision indicator.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 10, Lemma V.7, Eq. (31)

import Mathlib
import Definitions.Def_GoTBandit_Main_GoTChain

namespace GoTBandit.Main

/-- Lemma V.7, p. 10, Eq. (31): there is a universal constant `B0` such that, for large `k`, a
GoT run of `⌈c2 k^δ⌉` turns started from a law `ϕ` visits the optimal state at most
`(1 − η) π_{z*} ⌈c2 k^δ⌉` times with probability at most
`B0 ‖ϕ‖_π e^{−η² π_{z*} c2 k^δ / (72 T_m(1/8))}`. Disclosed: `ϕ` vanishes where `π` does;
`T_m(1/8)` is the worst-start total-variation mixing time. -/
theorem lemma_V_7 :
    ∃ B0 : ℝ, ∀ (N M : ℕ), N ≤ M → 2 ≤ M → ∀ c2 : ℕ, 0 < c2 → ∀ δ : ℝ, 0 < δ →
      ∀ η : ℝ, 0 < η → η < 1 → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∀ U : Fin N → Fin M → ℝ, (∀ n i, 0 < U n i) →
        ∀ aStar : Fin N → Fin M, IsOptimal U aStar → (∀ a, IsOptimal U a → a = aStar) →
        ∀ ε c : ℝ, 0 < ε → ε < 1 → 0 < c →
        ∀ π : Z N M → ℝ, MarkovMixing.IsStationary (gotMatrix U ε c) π →
        ∀ ϕ : Z N M → ℝ, MarkovMixing.IsDist ϕ → (∀ z, π z = 0 → ϕ z = 0) →
          pathProb (gotMatrix U ε c) ϕ (gotLen c2 δ k)
              {p | (visits (zStar aStar) p : ℝ) ≤
                (1 - η) * π (zStar aStar) * (gotLen c2 δ k : ℝ)} ≤
            B0 * normPi ϕ π *
              Real.exp (-(η ^ 2 * π (zStar aStar) * c2 * (k : ℝ) ^ δ) /
                (72 * (MarkovMixing.mixingTime (gotMatrix U ε c) π (1 / 8) : ℝ))) := by sorry

end GoTBandit.Main
