-- Prove2me | Theorems.Thm_LogMeanVar_Complete_theorem_2
-- name    : LogMeanVar.Complete.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:55.340822+00:00
-- url     : https://prove2.me/theorems/c5910daf-b9a6-46bb-a5b2-d0bc3fd05fa7
-- title:
--   Theorem 2, pp. 11–12 — π̂ ≡ (µ − r)/((1+γ)σ²) is an equilibrium strategy; its target annual return is the constant â ∈ (r, r + θ²/2)
-- statement:
--   Consider the log-return mean-variance criterion (7) subject to the log-return equation (6), in the complete market with constant interest rate $r$, stock drift $\mu$, volatility $\sigma>0$, preference parameter $\gamma>0$ (Assumption A) and horizon $T>0$, driven by a real Brownian motion $B$. Let
--   $$\hat\pi\equiv\frac{\mu-r}{(1+\gamma)\sigma^2},\qquad \theta=\frac{\mu-r}\sigma,\qquad \hat a=r+\Big(\frac1{1+\gamma}-\frac12\cdot\frac1{(1+\gamma)^2}\Big)\theta^2 .$$
--   Then:
--
--   1. **(i)** $\hat\pi$ is admissible, every perturbation $\pi^{h,v}$ of it ($t\in[0,T)$, $h>0$, $v\in\mathbb R$) is admissible, and $\hat\pi$ is an equilibrium strategy in the sense of Definition 1.
--   2. **(ii)** The target annual return of $\hat\pi$ is constant: for every $t\in[0,T)$, every starting log-wealth $y$ and every solution $\hat R$ of (6) under $\hat\pi$ started at $\hat R_t=y$, $\hat R_T$ is integrable and
--   $$\frac1{T-t}\,\mathbb E_t\big[\hat R_T-\hat R_t\big]=\hat a .$$
--   3. Moreover, if $\mu\ne r$, then $\hat a\in(r,r+\tfrac12\theta^2)$.
--
--   Part (i) identifies the dynamic mean-variance equilibrium for log returns with Merton's optimal strategy for CRRA utility with relative risk aversion $1+\gamma$; part (ii) gives the one-to-one link between the preference parameter $\gamma$ and the target return that the paper uses to elicit $\gamma$.
--
--   **Formalization Note** $\mathbb E_t$ is the mean of the process started at $(t,y)$ (Markovian reading); the complete market has no state variable $X$. Admissibility of $\hat\pi$ and of every perturbation is part of the conclusion, so the equilibrium claim cannot hold vacuously. The coordinates of $B$ are assumed measurable. The hypothesis $\mu\ne r$ is added for the interval only: for $\mu=r$, $\hat a=r$.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 11–12, Theorem 2

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 11–12, Theorem 2. Consider the mean-variance criterion (7) subject to (6) in the
complete market with constant `μ`, `r`, `σ > 0` and `γ > 0` (Assumption A).
(i) The constant fraction `π̂ ≡ (μ - r)/((1 + γ)σ²)` of (9) is an equilibrium strategy
(Definition 1); it is admissible, and so is every perturbation `π^{h,v}` (`h > 0`, `v ∈ ℝ`).
(ii) Its target annual return is constant: for every `t ∈ [0, T)`, every starting log-wealth
`y` and every solution `R̂` of (6) under `π̂` from `(t, y)`,
`(1/(T - t)) E_t[R̂_T - R̂_t] = â = r + (1/(1 + γ) - ½ · 1/(1 + γ)²) θ²` (10), `θ = (μ - r)/σ`.
Moreover `â ∈ (r, r + ½θ²)` when `μ ≠ r`.

**Formalization Note** `E_t` is the mean of the process started at `(t, y)` (Markovian
reading); there is no state `X` in the complete market. `B` is a real Brownian motion
(`IsBrownianReal`) with measurable coordinates. Admissibility is in the conclusion,
so the equilibrium claim is not vacuous. The hypothesis `μ ≠ r` is needed only for the
interval (for `μ = r`, `â = r`). -/
theorem theorem_2 (M : Market) (hM : M.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) :
    (Admissible M P B (fun _ _ => piHat M) ∧
      (∀ t ∈ Ico 0 M.T, ∀ h > (0 : ℝ), ∀ v : ℝ,
        Admissible M P B (spike (fun _ _ => piHat M) t h v)) ∧
      IsEquilibrium M P B (fun _ _ => piHat M)) ∧
    (∀ t ∈ Ico 0 M.T, ∀ y : ℝ, ∀ R : ℝ → Ω → ℝ,
      IsLogReturn M P B (fun _ _ => piHat M) t y R →
        Integrable (R M.T) P ∧ (∫ ω, (R M.T ω - y) ∂P) / (M.T - t) = aHat M) ∧
    (M.μ ≠ M.r → M.r < aHat M ∧ aHat M < M.r + theta M ^ 2 / 2) := by sorry

end LogMeanVar.Complete
