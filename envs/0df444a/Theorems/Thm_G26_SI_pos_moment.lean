-- Prove2me | Theorems.Thm_G26_SI_pos_moment
-- name    : G26.SI.pos_moment
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:31.945641+00:00
-- url     : https://prove2.me/theorems/baaa8ed6-6057-4f54-ad64-90a99fcc8184
-- title:
--   Killed positive moment of a scalar interface process with bounded drift
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space, $(\mathcal F_n)_{n\le N}$ are sub-$\sigma$-algebras, $Y_n:\Omega\to\mathbb R$ is a process, $I_n$ are *alive* events with $I_{n+1}\subseteq I_n$, and $\tau_n>0$, $\beta_n$, $B$ are reals. The **scalar interface** $\mathrm{SI}(m,N)$ asks that $Y_n$ and $I_n$ be $\mathcal F_n$-measurable, that $Y_n$ be a.s. bounded, and that for $m\le n\le N$ (resp. $m\le n<N$), almost surely on $I_n$,
--   $$
--   Y_n\ge\tau_n,\qquad |Y_{n+1}-Y_n|\le\frac{3Y_n}{B},\qquad \mathbb E\big[(Y_{n+1}-Y_n)^2\,\big|\,\mathcal F_n\big]\le 10\beta_n+\frac{2Y_n^2}{B(n+1)} .
--   $$
--
--   Write $\kappa^+_n=\mathbb E[\mathbf 1_{I_n}Y_n^{P}]$ (`kpos`). Assume $\mathrm{SI}(m,N)$ holds, $P\ge2$, $8P\le B$, $m\le t\le N$, $A\ge0$, and that $D_h(s)\ge0$ bounds the drift: a.s. on $I_n$, $\mathbb E[Y_{n+1}-Y_n\mid\mathcal F_n]\le D_h(n)$ for $m\le n<t$. Assume $\beta_n\ge0$, $D_h(s)+10(P-1)\beta_s/\tau_s\le A$ for $m\le s<t$, and $\kappa^+_m\le w_0^P$ for some $w_0>0$. With $\gamma=2(P-1)/B$,
--   $$
--   \mathbb E\big[\mathbf 1_{I_t}Y_t^{P}\big]\le\Big(\frac{A(t+1)}{1-\gamma}+w_0\Big(\frac{t+1}{m+1}\Big)^{2\gamma}\Big)^P .
--   $$
--
--   This is the upper local moment used for the compensated normalized variables on the alive window: the per-step growth is at most linear in time plus a slowly growing contribution of the starting value.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.28 (p.178), second estimate of (G.568), abstracted

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

theorem G26.SI.pos_moment [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : 8 * (P : ℝ) ≤ B) {t : ℕ} (hmt : m ≤ t) (htN : t ≤ N) {A : ℝ} (hA0 : 0 ≤ A)
    (Dh : ℕ → ℝ) (hDh : ∀ s, 0 ≤ Dh s)
    (hdr : ∀ n, m ≤ n → n < t → ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω ≤ Dh n)
    (hA : ∀ s, m ≤ s → s < t → Dh s + 10 * ((P : ℝ) - 1) * β s / τ s ≤ A)
    (hβ : ∀ n, 0 ≤ β n) {w0 : ℝ} (hw0 : 0 < w0) (hW0 : kpos μ Y I P m ≤ w0 ^ P) :
    kpos μ Y I P t ≤ (A * ((t : ℝ) + 1) / (1 - 2 * ((P : ℝ) - 1) / B) +
      w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * (2 * ((P : ℝ) - 1) / B))) ^ P := by sorry
