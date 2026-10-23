-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_IV_3_eq20
-- name    : GoTBandit.Main.lemma_IV_3_eq20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:24.574275+00:00
-- url     : https://prove2.me/theorems/3791fdc6-03c8-4c6f-b17e-54e5c9d13841
-- title:
--   Lemma IV.3, Eq. (20), p. 7 — the k-th exploration fails with probability ≤ 2NM e^{−w c1 (k/2)^δ k} + NM e^{−c1 (k/2)^δ k/(36M²)}
-- statement:
--   Consider $N\le M$ players running Algorithm 1 with i.i.d. rewards as in Definition II.1, exploration phases of length $\lceil c_1k^\delta\rceil$ with $c_1\ge1$ and $\delta>0$ (the remaining parameters $c_2,c_3,\varepsilon,c$ are arbitrary). Let $\mu^k_{n,i}$ be the estimates after the exploration phase of epoch $k\ge1$, $\sigma_{\max}=\max_{n,i}\sigma_{n,i}$, $b_{\max}=\max_{n,i}b_{n,i}$, $\Delta_{\min}$ the smallest utility gap, and
--
--   $$
--   w=\frac{\Delta_{\min}^2}{80M\,(4\sigma_{\max}^2+b_{\max}\Delta_{\min})}.
--   $$
--
--   Then
--
--   $$
--   P_{e,k}=\mathbb P\Big(\max_{n,i}|\mu^k_{n,i}-\mu_{n,i}|>\frac{\Delta_{\min}}4\Big)\le2NMe^{-wc_1(k/2)^\delta k}+NMe^{-\frac{c_1(k/2)^\delta}{36M^2}k}.
--   $$
--
--   The bound decays faster than any polynomial in $k$; it controls the cost of a failed exploration in the regret analysis.
--
--   **Formalization Note** When no player has two profiles of different utility ($N=M=1$, or $N=1$ with equal means) the minimum defining $\Delta_{\min}$ is over an empty set; Lean then gives $\Delta_{\min}=0$, so $w=0$ and the right side is at least $2NM$, and the inequality holds trivially, which is the paper's remark on p. 6 that the results of §IV "trivially hold" in this case. $\sigma_{\max}$ is the maximum of $\sqrt{\sigma^2_{n,i}}$. The estimate takes the junk value $0$ for an arm never visited without collision; such an arm counts as a failure.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 7, Lemma IV.3, Eqs. (19)–(20)

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm

open Finset MeasureTheory ProbabilityTheory

namespace GoTBandit.Main

/-- Lemma IV.3, p. 7, Eq. (20): after the exploration phase of epoch `k`, some estimate is off
by more than `∆min/4` with probability at most
`2NM e^{−w c1 (k/2)^δ k} + NM e^{−(c1 (k/2)^δ/(36M²)) k}`, where
`w = ∆min²/(80M(4σmax² + bmax ∆min))`. -/
theorem lemma_IV_3_eq20 {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k) :
    P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ k n i ω - μ n i|} ≤
      2 * N * M * Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i)) *
          p.c1 * ((k : ℝ) / 2) ^ p.δ * k) +
        N * M * Real.exp (-((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) * k) := by sorry

end GoTBandit.Main
