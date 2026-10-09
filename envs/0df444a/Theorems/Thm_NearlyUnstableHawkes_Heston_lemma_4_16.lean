-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_16
-- name    : NearlyUnstableHawkes.Heston.lemma_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:29.291013+00:00
-- url     : https://prove2.me/theorems/f01d2081-8d31-4f2a-86b9-edb52bed6c50
-- title:
--   Lemma 4.16, p. 30 — R^T_t = ∫_0^t ∫_{T(t−u)}^∞ ψ^T(s) ds d(M̄^{T+}_u − M̄^{T−}_u) converges u.c.p. to 0 on [0,1]
-- statement:
--   Under (3) and Assumptions 3 and 4, with $\psi^T=\sum_{k\ge1}(\phi^T_1-\phi^T_2)^{*k}$ and $\overline M^{T\pm}_t=M^{T\pm}_{Tt}/T$, the process
--   $$R^T_t=\int_0^t\int_{T(t-u)}^{+\infty}\psi^T(s)\,ds\;d\big(\overline M^{T+}_u-\overline M^{T-}_u\big)$$
--   converges uniformly in probability to $0$ on $[0,1]$.
--
--   $R^T$ is the second term of the decomposition of $P^T$ in Step 6; the lemma shows it does not contribute to the limit.
--
--   **Formalization Note** $\int_0^t g(u)\,d(\overline M^{T+}_u-\overline M^{T-}_u)$ is $\frac1T\int_0^{tT}g(s/T)\,(dM^{T+}_s-dM^{T-}_s)$, a pathwise Stieltjes integral. The inner integral is a Lebesgue integral over $(T(t-u),\infty)$ of the absolutely integrable signed resolvent.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 30, Lemma 4.16

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Lemma 4.16, p. 30: `R^T_t = ∫_0^t ∫_{T(t−u)}^{+∞} ψ^T(s) ds d(M̄^{T+}_u − M̄^{T−}_u)`
converges u.c.p. to `0` on `[0, 1]`. -/
theorem lemma_4_16
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    TendstoUCP01Zero P (fun n => remainderR (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n)) := by sorry

end NearlyUnstableHawkes.Heston
