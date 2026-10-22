-- Prove2me | Theorems.Thm_KMNewsvendor_radius_ge_quantile
-- name    : KMNewsvendor.radius_ge_quantile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T03:26:38.786691+00:00
-- url     : https://prove2.me/theorems/a5b95c66-2b1e-46e1-9009-6cecb7facfbb
-- title:
--   Lemma 2 (ii) — the convergence radius covers the newsvendor quantile, $\mathcal R\ge\psi^*$
-- statement:
--   Let the demands $D_1,D_2,\dots$ be independent copies of a nonnegative integer-valued random variable $D$ with $P[D=0]=0$, let $h,b>0$, $r^*=b/(b+h)$, and let $\psi^*$ be the newsvendor quantile. Run the KM-myopic policy with target ratio $r^*$ and an initial order $y_1\ge1$, and let $\mathcal R$ be its convergence radius. Then
--   $$\mathcal R\ge\psi^* .$$
--   Equivalently, with probability one the policy orders at least $\psi^*$ units in infinitely many periods. Together with Lemma 2 (i) this places the newsvendor quantile inside the interval on which the policy's estimators are consistent.
--
--   **Formalization Note** The hypotheses $P[D=0]=0$ and $y_1\ge1$ are added to the printed statement, which is false without them. If $y_1=0$, or if $D_1=0$ (an event of positive probability when $P[D=0]>0$), the first observation is an uncensored $0$ or the order is $0$; from then on every observation is $0$, the estimator is constant in $d$, and both the quantile order and the fallback $2Z_{(T)}$ equal $0$, so the policy orders $0$ forever and $\mathcal R=0<\psi^*$ whenever $\psi^*\ge1$. Time is $0$-based in Lean.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 935, Lemma 2 (ii) (with added hypotheses P[D = 0] = 0 and y_1 >= 1)

import Mathlib
import Definitions.Def_KMNewsvendor_quantile
import Definitions.Def_KMNewsvendor_kmSurv
import Definitions.Def_KMNewsvendor_kmOrder
import Definitions.Def_KMNewsvendor_radius
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Lemma 2 (ii) (p. 935), with the added hypotheses `P[D = 0] = 0` and `1 ≤ y₁` (without them
the printed statement is false: an uncensored zero observation absorbs the policy at `0`):
the convergence radius is at least the newsvendor quantile, `ℛ ≥ ψ*`. -/
theorem radius_ge_quantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (y₁ : ℕ)
    (hD0 : μ {ω | D 0 ω = 0} = 0) (hy₁ : 1 ≤ y₁) :
    quantile μ (D 0) (critRatio b h) ≤ radius μ D (critRatio b h) y₁ := by sorry

end KMNewsvendor
