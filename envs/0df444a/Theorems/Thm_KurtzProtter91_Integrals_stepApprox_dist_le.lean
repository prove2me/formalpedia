-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_stepApprox_dist_le
-- name    : KurtzProtter91.Integrals.stepApprox_dist_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:15:44.705969+00:00
-- url     : https://prove2.me/theorems/d21d0ffc-0755-4ebc-9f93-db84aea9c764
-- title:
--   Section 6, p. 1066 — the step approximation stays within ε: r(z(t), I_ε(z)(t)) ≤ ε
-- statement:
--   Let $E$ be a metric space with metric $r$, let $\varepsilon>0$ and let $\theta_k\in[\tfrac12,1]$ for every $k$. For every cadlag $z\in D_E[0,\infty)$ the step approximation $I_\varepsilon(z)$ of §6 satisfies
--   $$r\big(z(t),I_\varepsilon(z)(t)\big)\le\varepsilon\qquad\text{for all }t\ge0.$$
--
--   This is the uniform closeness used in the proof of Theorem 2.2, where $|X_n-X_n^\varepsilon|\le\varepsilon$ feeds the estimate (2.7).
--
--   **Formalization Note** The thresholds are a deterministic sequence with values in $[\tfrac12,1]$, the support of the paper's random $\theta_k$, so the statement holds for every realization.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1066, Section 6 (Uniform approximation by step functions)

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_StepApprox

open Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem stepApprox_dist_le {E : Type*} [MetricSpace E] (ε : ℝ) (hε : 0 < ε) (θ : ℕ → ℝ)
    (hθ : ∀ k, θ k ∈ Set.Icc (1 / 2 : ℝ) 1) (z : ℝ≥0 → E) (hz : IsCadlag z) (t : ℝ≥0) :
    dist (z t) (stepApprox ε θ z t) ≤ ε := by sorry

end KurtzProtter91.Integrals
