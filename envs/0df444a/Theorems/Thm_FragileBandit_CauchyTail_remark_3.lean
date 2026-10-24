-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_remark_3
-- name    : FragileBandit.CauchyTail.remark_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:51.798856+00:00
-- url     : https://prove2.me/theorems/b7008e2d-3004-470c-9bc0-fb46713273df
-- title:
--   Remark 3, p. 28 — the one-sided WLLN (32) plus convergence of E[N_i(T)]/log T gives the two-sided WLLN
-- statement:
--   **From a one-sided to a two-sided law of large numbers.** Let $\nu$ be any environment, $\pi$ any algorithm, $i$ an arm and $c \ge 0$. Suppose
--
--   $$\lim_{T\to\infty}\frac{\mathbb E_{\nu\pi}[N_i(T)]}{\log T} = c$$
--
--   and the one-sided weak law of (32) with $f = \log$ holds: for every $\epsilon \in (0,1)$, $\mathbb P_{\nu\pi}\big(N_i(T)/\log T \ge (1-\epsilon)c\big) \to 1$. Then $N_i(T)/\log T \to c$ in $\mathbb P_{\nu\pi}$-probability: for every $\delta > 0$,
--
--   $$\lim_{T\to\infty}\mathbb P_{\nu\pi}\Big(\Big|\frac{N_i(T)}{\log T} - c\Big| > \delta\Big) = 0.$$
--
--   This is the last sentence of Remark 3: for an optimized algorithm, Definition 2 gives the convergence of expectations with $c = 1/D_{\inf}$, Theorem 4 gives the one-sided law, and together they give the two-sided law (Lemma 4, and Lemma 2 in the exponential family), which the proof of Theorem 1 uses at the auxiliary environment $\tilde\nu$.
--
--   Differences from the source:
--   - generalization: an M-optimized algorithm (Definition 5) with c = 1/D_inf(P_i, µ*(ν), M), where (32) comes from Theorem 4 with f = log → any environment, algorithm, arm and c ≥ 0, with the convergence of E_νπ[N_i(T)]/log T to c and the one-sided law (32) as hypotheses; reason: Definition 5 is exactly the convergence of expectations with c = 1/D_inf, and Theorem 4 supplies (32), so Remark 3's implication is the special case
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 28, Remark 3 (last two sentences)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Remark 3 (p. 28): the "one-sided" WLLN (32) for `f = log`, together with the convergence
`E_νπ[N_i(T)] / log T → c`, implies the "two-sided" WLLN `N_i(T) / log T → c` in `P_νπ`-probability. -/
theorem remark_3 {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (hc : 0 ≤ c)
    (hE : Tendsto (fun T : ℕ => expPulls ν π T i / Real.log T) atTop (𝓝 c))
    (h32 : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      Tendsto (fun T : ℕ => banditMeasure ν π T
        {h | (1 - ε) * c ≤ (armPullCount i h : ℝ) / Real.log T}) atTop (𝓝 1)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | δ < |(armPullCount i h : ℝ) / Real.log T - c|}) atTop (𝓝 0) := by sorry

end FragileBandit.CauchyTail
