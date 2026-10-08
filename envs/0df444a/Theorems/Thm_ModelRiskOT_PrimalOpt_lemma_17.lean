-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_lemma_17
-- name    : ModelRiskOT.PrimalOpt.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:04:33.336987+00:00
-- url     : https://prove2.me/theorems/fe240c7f-00f5-4e98-a069-091da063fe09
-- title:
--   Lemma 17 — every feasible plan is improved by one concentrated on {f(y) ≥ f(x)}
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $\delta>0$, and let $c$ and $f$ satisfy (A1) and (A2). Then for every $\pi\in\Phi_{\mu,\delta}$ there is $\pi'\in\Phi_{\mu,\delta}$ concentrated on $\{(x,y)\in S\times S: f(y)\ge f(x)\}$, i.e. $\pi'\in\Phi'_{\mu,\delta}$, such that
--   $$\int f^+(y)\,d\pi'(x,y)\ge\int f^+(y)\,d\pi(x,y)\qquad\text{and}\qquad\int f^-(y)\,d\pi'(x,y)\le\int f^-(x)\,d\mu(x),\tag{55}$$
--   and moreover $\int f(y)\,d\pi'(x,y)\ge\int f(y)\,d\pi(x,y)$ whenever $\int f(y)\,d\pi(x,y)$ is well defined.
--
--   The lemma shows that the primal problem may be restricted to monotone plans, and that its value is never an $\infty-\infty$ ambiguity.
--
--   **Formalization Note** "Concentrated on" means measure one (p. 4). The last inequality is stated for every $\pi$, as $I(\pi)\le I(\pi')$ in `EReal`: when $\int f(y)\,d\pi$ is not well defined ($\infty-\infty$), $I(\pi)=-\infty$ by the `EReal` convention, so the unconditional statement is equivalent to the paper's.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 43, Appendix B.4, Lemma 17, Eq. (55)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PrimalFeasibleMono

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Lemma 17** (App. B.4, p. 43). Under (A1) and (A2), for every `π ∈ Φ_{μ,δ}` there is
`π′ ∈ Φ_{μ,δ}` concentrated on `{(x, y) : f(y) ≥ f(x)}` (i.e. `π′ ∈ Φ′_{μ,δ}`) with
`∫ f⁺(y) dπ′ ≥ ∫ f⁺(y) dπ` and `∫ f⁻(y) dπ′ ≤ ∫ f⁻ dμ` (55), and `I(π′) ≥ I(π)`. The last
inequality is stated for every `π`: when `∫ f(y) dπ` is not well defined (`∞ − ∞`), `I(π) = ⊥`. -/
theorem lemma_17 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (π : Measure (S × S)) (hπ : π ∈ ModelRiskOT.Duality.primalFeasible c μ δ) :
    ∃ π' ∈ primalFeasibleMono c f μ δ,
      ∫⁻ p, ENNReal.ofReal (f p.2) ∂π ≤ ∫⁻ p, ENNReal.ofReal (f p.2) ∂π' ∧
      ∫⁻ p, ENNReal.ofReal (-f p.2) ∂π' ≤ ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ∧
      ModelRiskOT.Duality.primalObj f π ≤ ModelRiskOT.Duality.primalObj f π' := by sorry

end ModelRiskOT.PrimalOpt
