-- Prove2me | Theorems.Thm_KMNewsvendor_km_myopic_tendsto_unique
-- name    : KMNewsvendor.km_myopic_tendsto_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T03:37:13.776507+00:00
-- url     : https://prove2.me/theorems/8c539b00-dc11-4bd4-a735-7c945e3892bf
-- title:
--   Corollary 1 — KM-myopic orders converge to the unique newsvendor quantile
-- statement:
--   Let the demands $D_1,D_2,\dots$ be independent copies of a nonnegative integer-valued random variable $D$ with $P[D=0]=0$, let $h,b>0$, $r^*=b/(b+h)$, and let $\psi^*$ be the newsvendor quantile. Assume that $\psi^*$ is the unique optimal order, i.e.
--   $$\bar F(\psi^*)<1-r^* .$$
--   Then the orders of the KM-myopic policy with target ratio $r^*$ and initial order $y_1\ge1$ satisfy, almost surely,
--   $$Y^{KM}_T\longrightarrow\psi^*\qquad(T\to\infty).$$
--   Since the orders are integers, this means that on almost every demand path the policy orders exactly $\psi^*$ from some period on: without knowing the demand distribution and seeing only censored sales, it learns the optimal newsvendor order.
--
--   **Formalization Note** Convergence is `Tendsto` in $\mathbb N$ with its discrete topology, which is the same as eventual equality. The hypotheses $P[D=0]=0$ and $y_1\ge1$ are added to the printed statement, which is false without them: an uncensored zero observation (or $y_1=0$) absorbs the policy at the order $0$ forever, while $\psi^*\ge1$ whenever $P[D=0]<r^*$. Time is $0$-based in Lean.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 936, Corollary 1 (with added hypotheses P[D = 0] = 0 and y_1 >= 1)

import Mathlib
import Definitions.Def_KMNewsvendor_quantile
import Definitions.Def_KMNewsvendor_kmSurv
import Definitions.Def_KMNewsvendor_kmOrder
import Definitions.Def_KMNewsvendor_radius
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Corollary 1 (p. 936), with the added hypotheses `P[D = 0] = 0` and `1 ≤ y₁`: if the
newsvendor quantile is the unique optimum, `F̄(ψ*) < 1 - r*`, the KM-myopic orders converge
almost surely to `ψ*` (in `ℕ`, i.e. they are eventually equal to `ψ*`). -/
theorem km_myopic_tendsto_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (y₁ : ℕ)
    (hD0 : μ {ω | D 0 ω = 0} = 0) (hy₁ : 1 ≤ y₁)
    (hunique : survival μ (D 0) (quantile μ (D 0) (critRatio b h)) < 1 - critRatio b h) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => kmOrder (critRatio b h) y₁ (fun t => D t ω) T)
      atTop (𝓝 (quantile μ (D 0) (critRatio b h))) := by sorry

end KMNewsvendor
