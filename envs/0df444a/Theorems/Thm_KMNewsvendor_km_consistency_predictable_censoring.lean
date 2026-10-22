-- Prove2me | Theorems.Thm_KMNewsvendor_km_consistency_predictable_censoring
-- name    : KMNewsvendor.km_consistency_predictable_censoring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T02:58:19.078212+00:00
-- url     : https://prove2.me/theorems/68a225de-6bce-40cd-a55e-1d1011c6ca88
-- title:
--   Theorem 2 — consistency of the Kaplan–Meier estimator under predictable censoring
-- statement:
--   Let $D_1,D_2,\dots$ be independent, identically distributed, nonnegative integer-valued random variables with law $D$, and let $Y_1,Y_2,\dots$ be real **censoring variables** such that each $Y_t$ is $\sigma(D_1,\dots,D_{t-1})$-measurable. Observe $Z_t=\min\{D_t,Y_t\}$ and $\delta_t=\mathbf 1[D_t\le Y_t]$, and let $\bar F_T$ be the Kaplan–Meier estimator built from the first $T$ observations. Then for every integer $d\ge0$ with
--   $$P[Y_t\ge d\ \text{i.o.}]=1$$
--   one has, almost surely,
--   $$\lim_{T\to\infty}\bar F_T(d)=\bar F(d)=P[D>d].$$
--
--   Classical consistency results for the Kaplan–Meier estimator assume censoring variables independent of the observations; here the censoring level of each period may depend on all previous demands, as it does when the censoring level is an order chosen by an adaptive policy.
--
--   **Formalization Note** Time is $0$-based: `Y t` is a measurable function of `D 0, …, D (t-1)`. The source states the conclusion for each $d\in[0,\mathcal R]$ with $\mathcal R=\max\{d:P[Y_t\ge d\text{ i.o.}]=1\}$; that maximum need not exist (for instance if $Y_t\to\infty$), so the statement is given for every integer $d$ satisfying the condition, which is the same statement whenever the maximum exists, since the condition is monotone in $d$. Integer $d$ suffice: for integer demand both $\bar F$ and $\bar F_T$ are constant on $[k,k+1)$.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 937, §5.1, Theorem 2

import Mathlib
import Definitions.Def_KMNewsvendor_quantile
import Definitions.Def_KMNewsvendor_kmSurv
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Theorem 2 (p. 937): consistency of the Kaplan–Meier estimator under predictable censoring.
The censoring level `Y t` of Lean period `t` is a measurable function of the demands `D i`, `i < t`.
For every `d` that is reached by the censoring levels infinitely often almost surely, the KM
estimator from the first `T` observations converges almost surely to `P[D > d]`. -/
theorem km_consistency_predictable_censoring {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, ∃ g : (Fin t → ℕ) → ℝ, Measurable g ∧ Y t = fun ω => g (fun i => D i ω))
    (d : ℕ) (hd : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, (d : ℝ) ≤ Y t ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        kmSurv T (fun t => min ((D t ω : ℕ) : ℝ) (Y t ω))
          (fun t => decide (((D t ω : ℕ) : ℝ) ≤ Y t ω)) d)
      atTop (𝓝 (survival μ (D 0) d)) := by sorry

end KMNewsvendor
