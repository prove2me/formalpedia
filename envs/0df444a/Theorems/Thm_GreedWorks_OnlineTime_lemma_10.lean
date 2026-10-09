-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_lemma_10
-- name    : GreedWorks.OnlineTime.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:56.429899+00:00
-- url     : https://prove2.me/theorems/7fb58272-ec96-4291-8a5e-3d46d7661de7
-- title:
--   Lemma 10, p. 22 — E[(X − µ)^+] ≤ µ√∆/2 (∆ ≤ 1) and ≤ µ∆/(∆+1) (∆ ≥ 1)
-- statement:
--   Let $X$ be a nonnegative random variable with finite second moment and mean $\mu=\mathbb E[X]>0$, and let $\Delta=\operatorname{Var}[X]/\mu^2$ be its squared coefficient of variation. Then
--   $$\mathbb E\big[(X-\mu)^+\big]\le\begin{cases}\mu\,\dfrac{\sqrt\Delta}{2},&\Delta\le1,\\[6pt]\mu\,\dfrac{\Delta}{\Delta+1},&\Delta\ge1.\end{cases}$$
--
--   Equivalently $\mathbb E[(X-\mu)^+]\le(h(\Delta)-1)\,\mu$; this is how the delay a job can cause beyond its mean is controlled in the stochastic analysis.
--
--   **Formalization Note** The squared coefficient of variation is undefined at $\mu=0$, so $\mu>0$ is assumed. $(x)^+=\max(x,0)$. A finite second moment makes the variance finite.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 22, Appendix A, Lemma 10, (20)

import Mathlib

namespace GreedWorks.OnlineTime

open MeasureTheory ProbabilityTheory

/-- Lemma 10 (p. 22). Let `X ≥ 0` be a random variable with finite second moment and mean
`μ = 𝔼[X] > 0`, and let `Δ = Var[X]/μ²` be its squared coefficient of variation. Then
`𝔼[(X − μ)⁺] ≤ μ √Δ / 2` if `Δ ≤ 1`, and `𝔼[(X − μ)⁺] ≤ μ Δ / (Δ + 1)` if `Δ ≥ 1`. -/
theorem lemma_10 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hX : MemLp X 2 Pr) (hμ : 0 < ∫ ω, X ω ∂Pr) :
    (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 ≤ 1 →
      ∫ ω, max (X ω - ∫ ω', X ω' ∂Pr) 0 ∂Pr ≤
        (∫ ω, X ω ∂Pr) * Real.sqrt (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2) / 2) ∧
    (1 ≤ variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 →
      ∫ ω, max (X ω - ∫ ω', X ω' ∂Pr) 0 ∂Pr ≤
        (∫ ω, X ω ∂Pr) * (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2) /
          (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 + 1)) := by sorry

end GreedWorks.OnlineTime
