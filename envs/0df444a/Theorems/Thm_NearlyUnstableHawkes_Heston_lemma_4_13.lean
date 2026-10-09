-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_13
-- name    : NearlyUnstableHawkes.Heston.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:12.91692+00:00
-- url     : https://prove2.me/theorems/33cd7935-5511-405a-9fd9-60babb05c11a
-- title:
--   Lemma 4.13, p. 28 — [(B^i)^T, (B^j)^T]_t → t 1_{i=j} in probability
-- statement:
--   Under (3) and Assumptions 3 and 4, with $(N^{T+},N^{T-})$ the bidimensional Hawkes processes of §3.2, let
--   $$(B^1)^T_t=\int_0^{tT}\frac{dM^{T+}_s+dM^{T-}_s}{\sqrt{T(\lambda^{T+}_s+\lambda^{T-}_s)}},\qquad (B^2)^T_t=\int_0^{tT}\frac{dM^{T+}_s-dM^{T-}_s}{\sqrt{T(\lambda^{T+}_s+\lambda^{T-}_s)}},$$
--   and let $[(B^i)^T,(B^j)^T]_t$ be their quadratic co-variation at time $t$. Then for $i,j\in\{1,2\}$ and every $t\in[0,1]$,
--   $$[(B^i)^T,(B^j)^T]_t\longrightarrow t\,\mathbf 1_{i=j}\quad\text{in probability.}$$
--
--   Together with the boundedness of the jumps of $(B^i)^T$, this is the input of the martingale functional central limit theorem giving Lemma 4.14.
--
--   **Formalization Note** $(B^i)^T$ are pure-jump plus finite-variation processes, so their quadratic co-variation is the sum over the jump times $s\in(0,tT]$ of $\Delta(B^i)^T_s\,\Delta(B^j)^T_s=\frac{(\Delta N^{T+}_s\pm\Delta N^{T-}_s)(\Delta N^{T+}_s\pm\Delta N^{T-}_s)}{T(\lambda^{T+}_{s-}+\lambda^{T-}_{s-})}$, with the predictable (left-limit) intensities, as the integrand of a stochastic integral. Indices $i,j\in\{1,2\}$ are $0,1$ in Lean. Convergence in probability is $\mathbb P(|[\cdot]_t-t\mathbf 1_{i=j}|>\varepsilon)\to0$ for every $\varepsilon>0$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 28, Lemma 4.13

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Lemma 4.13, p. 28: for `i, j ∈ {1, 2}` (indices `0, 1` here) and `t ∈ [0, 1]`,
`[(B^i)^T, (B^j)^T]_t → t 1_{i=j}` in probability. -/
theorem lemma_4_13
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    ∀ i j : Fin 2, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {ω | ε <
        |bracketT (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n) i j t ω - (if i = j then t else 0)|})
        atTop (𝓝 0) := by sorry

end NearlyUnstableHawkes.Heston
