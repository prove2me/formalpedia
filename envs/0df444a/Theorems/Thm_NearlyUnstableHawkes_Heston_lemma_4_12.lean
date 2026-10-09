-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_12
-- name    : NearlyUnstableHawkes.Heston.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:19.89898+00:00
-- url     : https://prove2.me/theorems/b9e5fadf-ccd7-4860-872f-26ccc39e2be9
-- title:
--   Lemma 4.12, p. 27 — X^T_s = (λ^{T+}_{sT} − λ^{T−}_{sT})/T converges u.c.p. to 0 on [0,1]
-- statement:
--   Let $T=T_n\to\infty$ and assume (3), $T(1-a_T)\to\lambda>0$, and Assumptions 3 and 4. For each $T$ let $(N^{T+},N^{T-})$ be the bidimensional Hawkes process on $[0,T]$ with baseline $\mu>0$ and kernels $\phi^T_i=a_T\phi_i$, and set
--   $$X^T_s=\frac{\lambda^{T+}_{sT}-\lambda^{T-}_{sT}}{T},\qquad s\in[0,1].$$
--   Then $X^T$ converges uniformly in probability to $0$ on $[0,1]$: for every $\varepsilon>0$,
--   $$\mathbb P\Big(\sup_{s\in[0,1]}|X^T_s|>\varepsilon\Big)\longrightarrow0 .$$
--
--   The imbalance between the two intensities is negligible at the scale $T$; this is used to show that the brackets of $(B^1)^T$ and $(B^2)^T$ decouple.
--
--   **Formalization Note** The probability of the event $\{\exists s\in[0,1]:|X^T_s|>\varepsilon\}$ is the measure of that set (an outer measure if it were not measurable). The Hawkes processes live on probability spaces that may vary with $T$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 27, Lemma 4.12

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Lemma 4.12, p. 27: the process `X^T_s = (λ^{T+}_{sT} − λ^{T−}_{sT})/T` converges u.c.p.
to `0` on `[0, 1]`. -/
theorem lemma_4_12
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    TendstoUCP01Zero P (fun n => imbalanceProc (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n)) := by sorry

end NearlyUnstableHawkes.Heston
