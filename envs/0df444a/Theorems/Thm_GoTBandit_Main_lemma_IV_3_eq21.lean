-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_IV_3_eq21
-- name    : GoTBandit.Main.lemma_IV_3_eq21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:33.22099+00:00
-- url     : https://prove2.me/theorems/aac267a8-1e9e-426f-ac4d-634278a2c124
-- title:
--   Lemma IV.3, Eq. (21), p. 7 — one of the last ⌊k/2⌋ + 1 explorations fails with exponentially small probability
-- statement:
--   In the setting of Lemma IV.3, Eq. (20) (Algorithm 1 with i.i.d. rewards, $c_1\ge1$, $\delta>0$, epoch $k\ge1$, and $w$ as in Eq. (19)), and assuming $\Delta_{\min}>0$, the probability that at least one of the exploration phases of the epochs $k-r$, $r=0,\dots,\lfloor k/2\rfloor$, ends with some estimate off by more than $\Delta_{\min}/4$ satisfies
--
--   $$
--   \mathbb P\Big(\bigcup_{r=0}^{\lfloor k/2\rfloor}P_{e,k-r}\Big)\le\frac{2NM}{1-e^{-wc_1(k/4)^\delta}}e^{-\frac w2c_1(k/4)^\delta k}+\frac{NM}{1-e^{-\frac1{36M^2}c_1(k/4)^\delta}}e^{-\frac1{72M^2}c_1(k/4)^\delta k}.
--   $$
--
--   Here $\mathbb P(\bigcup P_{e,k-r})$ is the paper's shorthand for the probability of the union of the failure events $\{\max_{n,i}|\mu^{k-r}_{n,i}-\mu_{n,i}|>\Delta_{\min}/4\}$.
--
--   The exploitation phase of epoch $k$ uses the GoT phases of the last $\lfloor k/2\rfloor+1$ epochs, so all their explorations must succeed; this bound is the first term of the per-epoch regret bound (11).
--
--   **Formalization Note** The hypothesis $\Delta_{\min}>0$ is added. The minimum defining $\Delta_{\min}$ can be over an empty set ($N=M=1$, or $N=1$ with equal means); with Lean's junk value $0$ one gets $w=0$, the first denominator vanishes, and the inequality would be false although the event has probability close to $1$. For $N\ge2$ the hypothesis holds automatically (a collision gives utility $0$ while every mean is positive). It makes $w>0$, so the denominators are positive.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 7, Lemma IV.3, Eq. (21)

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm

open Finset MeasureTheory ProbabilityTheory

namespace GoTBandit.Main

/-- Lemma IV.3, p. 7, Eq. (21): some exploration phase among the last `⌊k/2⌋ + 1` epochs fails
(some estimate off by more than `∆min/4`) with probability at most
`(2NM/(1 − e^{−w c1 (k/4)^δ})) e^{−(w/2) c1 (k/4)^δ k}
  + (NM/(1 − e^{−(1/(36M²)) c1 (k/4)^δ})) e^{−(1/(72M²)) c1 (k/4)^δ k}`.
Disclosed addition: `0 < ∆min` (otherwise `w = 0` and the first denominator vanishes). -/
theorem lemma_IV_3_eq21 {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (hΔ : 0 < Δmin μ)
    (k : ℕ) (hk : 1 ≤ k) :
    P.real {ω | ∃ j ≤ k / 2,
        Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} ≤
      2 * N * M / (1 - Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i)) *
            p.c1 * ((k : ℝ) / 4) ^ p.δ)) *
          Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i) / 2) *
            p.c1 * ((k : ℝ) / 4) ^ p.δ * k) +
        N * M / (1 - Real.exp (-(1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ)) *
          Real.exp (-(1 / (72 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ * k) := by sorry

end GoTBandit.Main
