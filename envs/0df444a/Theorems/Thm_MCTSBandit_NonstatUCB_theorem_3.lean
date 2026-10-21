-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_theorem_3
-- name    : MCTSBandit.NonstatUCB.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:00.370066+00:00
-- url     : https://prove2.me/theorems/8bcb286c-e5b2-499b-a6a5-15960f707232
-- title:
--   Theorem 3 — convergence and polynomial concentration of UCB reward
-- statement:
--   Consider a non-stationary $K$-armed bandit satisfying (12)–(13), with bounded rewards and a unique limiting-optimal arm $i_*$. Apply rule (15) using the polynomial bonus (16), with $\xi\eta(1-\eta)\le\alpha<\xi(1-\eta)$ and $\alpha>2$. Writing $\Delta$ for a positive lower bound on every suboptimality gap, the theorem gives both conclusions.
--
--   First, for $n\ge1$,
--   $$\left|\mathbb E[\bar X_n]-\mu_*\right|\le\left|\mathbb E[\bar X_{i_*,n}]-\mu_*\right|+\frac{2R(K-1)}{n}\left[\left(\frac{2}{\Delta}\beta^{1/\xi}\right)^{1/(1-\eta)}n^{\alpha/(\xi(1-\eta))}+\frac{2}{\alpha-2}+1\right].$$
--
--   Second, there is one $\beta'>1$, depending only on $R,K,\Delta,\beta,\xi,\alpha,\eta$, such that for every admissible bandit and run, every $n,z\ge1$, both tails of $n\bar X_n-n\mu_*$ beyond $n^{\eta'}z$ are at most $\beta'/z^{\xi'}$, where $\eta'=\alpha/(\xi(1-\eta))\in[1/2,1)$ and $\xi'=\alpha-1>0$.
--
--   The two parts are the paper's convergence and concentration guarantees for the non-stationary UCB process.
--
--   **Formalization Note** The paper's $\Delta_{\min}$ is generalized to a gap lower bound $\Delta$; taking $\Delta=\Delta_{\min}$ recovers the printed result. The Lean statement requires $K\ge1$, positive play horizons, and measurable arm choices. No independence is assumed. The single constant $\beta'$ is chosen before the probability space, rewards, run, horizon and tail threshold.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, pp. 16–17, Theorem 3, parts A and B

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, Theorem 3, pp. 16–17, both parts. -/
theorem theorem_3 (K : ℕ) (hK : 1 ≤ K) (R β ξ η α Δ : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α) (hΔ : 0 < Δ) :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar : Fin K)
      (I : ℕ → Ω → Fin K),
      IsNonstatMAB P X μ R β ξ η → GapLB μ istar Δ →
      IsUCBRun X β ξ α η I → RunMeasurable I →
      ∀ n : ℕ, 1 ≤ n →
        |(∫ ω, runAvg X I n ω ∂P) - μ istar| ≤
          |(∫ ω, empMean X istar n ω ∂P) - μ istar| +
          2 * R * ((K : ℝ) - 1) *
            (((2 / Δ) * β ^ (1 / ξ)) ^ (1 / (1 - η)) *
              (n : ℝ) ^ (α / (ξ * (1 - η))) + 2 / (α - 2) + 1) / (n : ℝ)) ∧
    (∃ β' : ℝ, 1 < β' ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar : Fin K)
        (I : ℕ → Ω → Fin K),
        IsNonstatMAB P X μ R β ξ η → GapLB μ istar Δ →
        IsUCBRun X β ξ α η I → RunMeasurable I →
        ∀ n : ℕ, 1 ≤ n → ∀ z : ℝ, 1 ≤ z →
          (P {ω | (n : ℝ) ^ (α / (ξ * (1 - η))) * z ≤
              (n : ℝ) * runAvg X I n ω - (n : ℝ) * μ istar}
            ≤ ENNReal.ofReal (β' / z ^ (α - 1))) ∧
          (P {ω | (n : ℝ) * runAvg X I n ω - (n : ℝ) * μ istar ≤
              -((n : ℝ) ^ (α / (ξ * (1 - η))) * z)}
            ≤ ENNReal.ofReal (β' / z ^ (α - 1)))) ∧
    0 < α - 1 ∧
    (1 / 2 : ℝ) ≤ α / (ξ * (1 - η)) ∧
    α / (ξ * (1 - η)) < 1 := by sorry

end MCTSBandit.NonstatUCB
