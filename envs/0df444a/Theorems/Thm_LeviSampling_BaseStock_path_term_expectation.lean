-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_path_term_expectation
-- name    : LeviSampling.BaseStock.path_term_expectation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:19.929276+00:00
-- url     : https://prove2.me/theorems/8efbcd75-d7d7-4df5-a12e-232a5b042eca
-- title:
--   Lemma 3.4 — the path variable M̃ʳ is an unbiased estimate
-- statement:
--   Let the demands $D_0, \dots, D_{T-1}$ be independent with laws $\mu_0, \dots, \mu_{T-1}$, let $L$ be any vector of levels, $y \in \mathbb R$ and periods $t < j < T$ ($0$-based). Then
--   $$\mathbb E\big[\tilde M^r_{tj}(y)\big] = \mathbb E\big[\mathbb 1(\tilde A_{jt}(y))\, C^r_j(y - D_{[t,j)})\big],$$
--   where $\tilde M^r_{tj}(y) = \mathbb 1(\tilde A_{jt}(y))(-b_j + (h_j + b_j)\mathbb 1(D_j \le y - D_{[t,j)}))$, $\tilde A_{jt}(y)$ is the event that $y - D_{[t,k)} \ge L_k$ for all $t < k \le j$, and $C^r_j(x) = -b_j + (b_j + h_j)\Pr(D_j \le x)$.
--
--   **Formalization Note** The expectation is over one sample path with law $\mu_0 \otimes \dots \otimes \mu_{T-1}$. Both integrands are bounded, so no moment hypothesis is needed. The paper's $t = 1, \dots, T-1$, $j > t$ is $t < j < T$ here.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 834, Lemma 3.4

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Estimator

open MeasureTheory

namespace LeviSampling.BaseStock

open Classical in
/-- **Lemma 3.4** (Levi, Roundy & Shmoys 2007, p. 834), 0-based periods. For periods
`t < j < T`, levels `L` and a point `y`, the variable
`M̃^r_{tj}(y) = 𝟙(Ã_{jt}(y)) (-b_j + (h_j + b_j) 𝟙(D_j ≤ y - D_{[t,j)}))` has expectation
`E[𝟙(Ã_{jt}(y)) C^r_j(y - D_{[t,j)})]`, where `C^r_j(x) = -b_j + (b_j + h_j) Pr(D_j ≤ x)` and the
demands `D_0, …, D_{T-1}` are independent with laws `μ 0, …, μ (T-1)`. -/
theorem path_term_expectation (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b : ℕ → ℝ) (L : ℕ → ℝ) (t j : ℕ) (htj : t < j) (hj : j < T) (y : ℝ) :
    ∫ p, pathTerm h b L (extendPath p) t j y ∂(pathLaw T μ) =
      ∫ p, (if reachEvent L (extendPath p) t j y then
              nvRightDeriv (μ j) (h j) (b j) (y - cumDemand (extendPath p) t j)
            else 0) ∂(pathLaw T μ) := by sorry

end LeviSampling.BaseStock
