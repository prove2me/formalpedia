-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_theorem_b_1
-- name    : MemSampleNGCA.Main.theorem_b_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:17.555592+00:00
-- url     : https://prove2.me/theorems/fe83ed2a-1a74-4341-85d3-5fb9f99e3109
-- title:
--   Theorem B.1 — KL(µ_N, ν_N) ≤ N·T_KL(2h) + log M (Ne^{−h} + 2N²[Me^{−h} + 2^B T_q(4h)^N e^{−qh/2}{1 + N(Me^{−h})^q}])
-- statement:
--   Let $\pi$ be a probability measure on a parameter space $\Theta$, $P_0$ a probability measure on $\mathcal X$, and $\{P_\theta\}_{\theta\in\Theta}$ a family with $0\le dP_\theta/dP_0\le M$ for every $\theta$. Let $q\ge2$ and $h\ge1$. For every single-pass streaming algorithm with $B$ bits of memory run on $N$ samples, let $\mu_N$ and $\nu_N$ be the laws (14) of the final memory state under the mixture $\int P_\theta\,\pi(d\theta)$ and under $P_0$. Then
--   $$\mathrm{KL}(\mu_N,\nu_N)\le N\cdot T_{KL}(2h)+\log M\Big(Ne^{-h}+2N^2\big[Me^{-h}+2^BT_q(4h)^Ne^{-qh/2}\{1+N(Me^{-h})^q\}\big]\Big),$$
--   with $T_{KL}$ and $T_q$ the functionals (17a)–(17b).
--
--   This is the paper's general memory–sample tradeoff. A small $\mathrm{KL}(\mu_N,\nu_N)$ means the memory state cannot tell the null from the mixture, so no tester succeeds. The bound is small unless $B$ is large compared with $qh$, provided $T_{KL}(2h)$ and $\log T_q(4h)$ are small, which Appendix C establishes for NGCA.
--
--   Differences from the source:
--   - generalization: π is the uniform measure on Θ ⊆ S^{d−1} → π is any probability measure on a measurable space Θ; reason: the proof uses only that π is a probability measure; the uniform measure is an instance
--   - encoding: a family {P_θ} with 0 ≤ dP_θ/dP_0 ≤ M → IsBoundedDensityFamily π P_0 p M; reason: as in Lemma B.2
--   - encoding: Definition 1.7 → StreamingAlg; reason: as in Lemma B.2
--   - encoding: F_h = {f : Θ → ℝ_{≥0} : ∫ f dπ = 1, f ≤ e^h} → measurable f : Θ → ℝ≥0∞ with ∫ f dπ = 1 and f ≤ e^h; reason: a density must be measurable for P_f to be defined; the bound makes f finite
--   - encoding: KL, T_KL, T_q and the right-hand side real → klDiv, ⨆ and arithmetic in ℝ≥0∞, log M as ENNReal.ofReal (log M); reason: M ≥ 1 is forced by ∫ p(θ,·) dP_0 = 1, so log M ≥ 0 and every term is the paper's real value; T_q ≤ M^q is finite, so no 0·∞ convention applies
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 17 (PDF 19), Theorem B.1

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Theorem B.1 (p. 17, PDF 19): for `q ≥ 2`, `h ≥ 1` and `0 ≤ dP_θ/dP₀ ≤ M`, every single-pass
streaming algorithm with `B` bits of memory and `N` samples satisfies
`KL(µ_N, ν_N) ≤ N · T_KL(2h) + log M · (N e^{−h} + 2N² [M e^{−h} + 2^B T_q(4h)^N e^{−qh/2} {1 + N (M e^{−h})^q}])`. -/
theorem theorem_b_1 {Θ : Type*} [MeasurableSpace Θ] {X : Type*} [MeasurableSpace X]
    {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (M : ℝ)
    (hF : IsBoundedDensityFamily π P₀ p M) (q h : ℝ) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (A : StreamingAlg B X Ω) (N : ℕ) :
    InformationTheory.klDiv (muMeas A N π P₀ p N) (nuMeas A N P₀ N) ≤
      (N : ℝ≥0∞) * TKL π P₀ p (2 * h) + ENNReal.ofReal (Real.log M) *
        ((N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-h)) +
          2 * (N : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (M * Real.exp (-h)) +
            2 ^ B * Tq π P₀ p q (4 * h) ^ N * ENNReal.ofReal (Real.exp (-(q * h / 2))) *
              (1 + (N : ℝ≥0∞) * ENNReal.ofReal ((M * Real.exp (-h)) ^ q)))) := by sorry

end MemSampleNGCA.Main
