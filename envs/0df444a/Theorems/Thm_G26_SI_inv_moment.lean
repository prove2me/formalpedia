-- Prove2me | Theorems.Thm_G26_SI_inv_moment
-- name    : G26.SI.inv_moment
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:40.231186+00:00
-- url     : https://prove2.me/theorems/e8ca4f93-02f3-4b12-99ea-cc9e894f9a7c
-- title:
--   Killed inverse moment of a scalar interface process with positive drift
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space, $(\mathcal F_n)_{n\le N}$ are sub-$\sigma$-algebras, $Y_n:\Omega\to\mathbb R$ is a process, $I_n$ are *alive* events with $I_{n+1}\subseteq I_n$, and $\tau_n>0$, $\beta_n$, $B$ are reals. The **scalar interface** $\mathrm{SI}(m,N)$ asks that $Y_n$ and $I_n$ be $\mathcal F_n$-measurable, that $Y_n$ be a.s. bounded, and that for $m\le n\le N$ (resp. $m\le n<N$), almost surely on $I_n$,
--   $$
--   Y_n\ge\tau_n,\qquad |Y_{n+1}-Y_n|\le\frac{3Y_n}{B},\qquad \mathbb E\big[(Y_{n+1}-Y_n)^2\,\big|\,\mathcal F_n\big]\le 10\beta_n+\frac{2Y_n^2}{B(n+1)} .
--   $$
--
--   Write $\kappa^-_n=\mathbb E[\mathbf 1_{I_n}Y_n^{-P}]$ (`kinv`). Assume $\mathrm{SI}(m,N)$ holds, $P\ge2$, $3P/B\le1/2$, $8(P+1)\le B$, and $\Delta>0$. Let $m\le t\le N$ with $2(m+1)\le t+1$, $(P+1)\Delta\le\tau_m$ and $P+1\le2(m+1)$. Assume that for $m\le n<t$ the conditional drift is at least $\Delta$ a.s. on $I_n$, $\mathbb E[Y_{n+1}-Y_n\mid\mathcal F_n]\ge\Delta$, and that $\beta_n\ge0$ with $40(P+1)\beta_n(n+1)\le\tau_n^2$. Then
--   $$
--   \mathbb E\big[\mathbf 1_{I_t}\,Y_t^{-P}\big]\le\Big(\frac{4}{(t+1)\Delta}\Big)^P .
--   $$
--
--   This is the inverse-moment estimate of Lemma G.22, isolated from the bandit run. Lemma G.29 applies it to the compensated per-action variables (with $\Delta$ a positive gap), and Lemma G.28 applies it to the normalized per-direction variables (with $\Delta=1$).
--
--   **Formalization Note** Rounds are 0-based, so $t+1$ plays the role of the paper's $t$. An inverse multiplied by a zero indicator is zero.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.22 (p.165), second display, and (G.568) of Lemma G.28 (p.178), abstracted

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set
open G26
variable {Ω : Type*}
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

theorem G26.SI.inv_moment [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : (P : ℝ) * (3 / B) ≤ 1 / 2) (hB8 : 8 * ((P : ℝ) + 1) ≤ B) {Δ : ℝ} (hΔ : 0 < Δ)
    {t : ℕ} (hmt : m ≤ t) (htN : t ≤ N) (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hτm : ((P : ℝ) + 1) * Δ ≤ τ m) (hmP : (P : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hdr : ∀ n, m ≤ n → n < t → ∀ᵐ ω ∂μ, ω ∈ I n → Δ ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω)
    (hτβ : ∀ n, m ≤ n → n < t → 40 * ((P : ℝ) + 1) * β n * ((n : ℝ) + 1) ≤ τ n ^ 2)
    (hβ : ∀ n, 0 ≤ β n) :
    kinv μ Y I P t ≤ (4 / (((t : ℝ) + 1) * Δ)) ^ P := by sorry
