-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_lemma_4_9
-- name    : NearlyUnstableHawkes.CIR.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:39.093514+00:00
-- url     : https://prove2.me/theorems/807ccd8e-797c-40da-8578-6e69644b2481
-- title:
--   Lemma 4.9 — fourth-moment increment bound for the error process
-- statement:
--   Let $Y^T$ be the rescaled Hawkes martingale error process. Under Assumptions 1–2 and $T(1-a_T)\to\lambda>0$, for each $\varepsilon>0$ there is a constant $c_\varepsilon>0$, independent of $T$, $t$, and $s$, such that for $T\ge1$ and $t,s\in[0,1]$,
--
--   $$\mathbb E[(Y^T_t-Y^T_s)^4]\le c_\varepsilon\left(|t-s|^{3/2-\varepsilon}+\frac{1}{T^2}|t-s|^{1-\varepsilon}\right).$$
--
--   This increment bound is the quantitative tightness input for the error process.
--
--   **Formalization Note** The fourth moment is an extended nonnegative integral, so a nonintegrable random variable cannot acquire a default-zero expectation. $T$ ranges over the observation-scale sequence.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 21, Lemma 4.9, display (9)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace NearlyUnstableHawkes.CIR

/-- Lemma 4.9, p. 21: the fourth-moment increment estimate (9). -/
theorem lemma_4_9 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ) (m lam μ : ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hμ : 0 < μ) (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) (hρ : Assumption2 T a φ)
    (hN : ∀ n, IsHawkes (P n) μ (fun s => a n * φ s) (T n) (N n)) :
    ∀ ε : ℝ, 0 < ε → ∃ cε : ℝ, 0 < cε ∧
      ∀ n : ℕ, 1 ≤ T n →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          (∫⁻ ω, ENNReal.ofReal
            ((Y T a φ m lam μ N n t ω - Y T a φ m lam μ N n s ω) ^ 4) ∂P n) ≤
            ENNReal.ofReal (cε *
              (|t - s| ^ ((3 / 2 : ℝ) - ε) +
                (1 / (T n) ^ 2) * |t - s| ^ (1 - ε))) := by sorry

end NearlyUnstableHawkes.CIR
