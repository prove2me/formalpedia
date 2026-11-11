-- Prove2me | Theorems.Thm_HighMagSampling_SK_theorem_4
-- name    : HighMagSampling.SK.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:28:46.356719+00:00
-- url     : https://prove2.me/theorems/4029713d-0a95-48ed-a8ad-f6cbeae491cb
-- title:
--   Theorem 4 — w.p. $\ge 1-\delta$ over $J\sim\mathrm{GOE}(d)$, the lazy down-up walk samples the fixed-magnetization SK measure for every $\beta$ and $k\le c\,d/(\bar\beta^2\log(e\bar\beta))$
-- statement:
--   Let $J\sim\mathrm{GOE}(d)$ (Model 1, the Sherrington–Kirkpatrick model). For $\beta>0$, $h\in\mathbb R^d$ and $k\in[d]$ let $\pi$ be the fixed-magnetization Ising measure $\pi(x)\propto\exp(\beta(\tfrac12x^\top Jx+h^\top x))$ on the Hamming slice $\mathcal X^d_k$, and let $\mathcal T^{\mathrm{DU},\pi}$ be its down-up walk. Write $\bar\beta=\max(1,\beta)$ and $\Delta=\sqrt{\log(d/\delta)/d}+\log(d/\delta)/d$.
--
--   There are universal constants $c>0$, $C'>0$ and $C_T>0$ such that for every $d\ge1$ and every $\delta\in(0,\tfrac12)$, with probability at least $1-\delta$ over $J$, the following holds simultaneously for every $\beta>0$, every $k\in[d]$ with
--   $$k\le\frac{c\,d}{\bar\beta^2\log(e\bar\beta)}\qquad\text{and}\qquad\Delta\le\frac1{C'\bar\beta^2\log(e\bar\beta)}\quad(31),$$
--   every $h\in\mathbb R^d$, every $T\in\mathbb N$ with
--   $$T\ \ge\ C_T\Big(k\log\frac1\delta+k^2\Big(\log d+\beta\Big(\|h\|_\infty+\sqrt{\log(d/\delta)}\Big)\Big)\Big),$$
--   and every initial distribution $\pi_0$ on $\mathcal X^d_k$:
--   $$\mathrm{TV}\Big(\big(\mathrm{lazy}(\mathcal T^{\mathrm{DU},\pi})\big)^T\pi_0,\ \pi\Big)\ \le\ \delta .$$
--
--   This is the paper's main result for Ising models: polynomial-time sampling of the SK model restricted to a linear-size magnetization slice at every inverse temperature, where unrestricted sampling is believed hard at low temperature.
--
--   **Formalization Note.** Model 1 is the published `RandMatDisc.goe d` and a sample $J$ is read as `Matrix.of J`; the GOE diagonal is kept, which does not change $\pi$ on the slice ($x_i^2=1$). TV is `PolySampIso.tvDist`. $\|h\|_\infty$ is $\sup_i|h_i|$ over the finite index set ($d\ge1$). Natural logarithms.
--
--   Differences from the source:
--   - reading: "with probability $\ge1-\delta$ … if $T=\Omega(\cdot)$ … for any $\pi_0$", with $\beta$, $k$, $h$ fixed in the hypotheses → one event of probability $\ge1-\delta$ on which the conclusion holds for every $\beta$, $k$, $h$, $T$, $\pi_0$ satisfying the conditions; reason: the stronger reading; the paper's failure event (Lemma 12) does not depend on them, and the remark after the proof uses this uniformity in $\beta$.
--   - encoding: "with probability $\ge1-\delta$" → the failure set has $\mathrm{GOE}(d)$-measure $\le\delta$; reason: equivalent for a measurable event, and does not presuppose measurability.
--   - encoding: $k=O(d/(\bar\beta^2\log(e\bar\beta)))$ "for a sufficiently small constant", $T=\Omega(\cdot)$ "for a sufficiently large constant", and the constant $C'$ of (31) → existentially quantified universal constants $c$, $C_T$, $C'>0$ chosen before $d$ and $\delta$; reason: each $O$/$\Omega$ is one universal constant (§2.1: formal statements have all dependences explicit).
--   - encoding: $\mathcal X^d_k$ as $\pm1$ vectors → `Slice d k`; reason: the paper's bijection $x\mapsto\mathrm{set}(x)$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 27, Theorem 4 (with Eq. (16), p. 15; Model 1, p. 12; Eq. (31), p. 26)

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp
import Definitions.Def_HighMagSampling_SK_Spectral

open MeasureTheory ProbabilityTheory

namespace HighMagSampling.SK

/-- Theorem 4, p. 27: there are universal constants `c, C', C_T > 0` such that for every `d ≥ 1`
and `δ ∈ (0, 1/2)`, outside a set of `GOE(d)`-measure at most `δ`, the matrix `J` has the
following property. For every `β > 0`, every `k ∈ [d]` with `k ≤ c d/(β̄² log(e β̄))` and
`Δ ≤ 1/(C' β̄² log(e β̄))` (condition (31)), every `h ∈ ℝ^d`, every
`T ≥ C_T (k log(1/δ) + k² (log d + β (‖h‖_∞ + √(log(d/δ)))))` and every `π₀ ∈ P(X^d_k)`,
`TV((lazy T^{DU,π})^T π₀, π) ≤ δ`, where `π` is the fixed-magnetization Ising measure (16). -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ C_T : ℝ, 0 < C_T ∧
      ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        RandMatDisc.goe d {J | ¬ ∀ β : ℝ, 0 < β → ∀ k : ℕ, 1 ≤ k → k ≤ d →
          (k : ℝ) ≤ c * d / (betaBar β ^ 2 * Real.log (Real.exp 1 * betaBar β)) →
          Delta d δ ≤ 1 / (C' * betaBar β ^ 2 * Real.log (Real.exp 1 * betaBar β)) →
          ∀ h : Fin d → ℝ, ∀ T : ℕ,
            C_T * ((k : ℝ) * Real.log (1 / δ) + (k : ℝ) ^ 2 * (Real.log d +
              β * ((⨆ i, |h i|) + Real.sqrt (Real.log (d / δ))))) ≤ T →
            ∀ π₀ : Measure (Slice d k), IsProbabilityMeasure π₀ →
              PolySampIso.tvDist
                (lawAfter (lazy (downUp (isingMeasure k β (Matrix.of J) h))) π₀ T)
                (isingMeasure k β (Matrix.of J) h) ≤ δ} ≤
          ENNReal.ofReal δ := by sorry

end HighMagSampling.SK
