-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_eq_4_35_optimal
-- name    : KallMayerSLP.CondExp.eq_4_35_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:06.38999+00:00
-- url     : https://prove2.me/theorems/e7249043-278c-4aaf-a1ce-4bdb234b17ba
-- title:
--   §4.3, p.163 — an optimal $z^*$ of (4.35) is an $\alpha$-quantile and gives $v_c(x^*,\alpha)$
-- statement:
--   Let $t(\xi)$, $h(\xi)$ be integrable, $\zeta(x,\xi)=t(\xi)^{\mathrm T}x-h(\xi)$, $0<\alpha<1$, and let $(x^*,z^*)$ with $x^*\in\mathcal B$ be an optimal solution of
--   $$
--   \min_{(x,z)}\ c^{\mathrm T}x+z+\frac{1}{1-\alpha}\,\mathbb E[(\zeta(x,\xi)-z)^+]\quad\text{s.t. }x\in\mathcal B. \tag{4.35}
--   $$
--   Then $z^*$ is an $\alpha$-quantile of $\Psi(x^*,\cdot)$, and
--   $$
--   v(x^*,\alpha)\le z^*,\qquad v_c(x^*,\alpha)=z^*+\frac{1}{1-\alpha}\,\mathbb E[(\zeta(x^*,\xi)-z^*)^+].
--   $$
--
--   So solving the joint program (4.35) delivers both risk values at the optimal decision.
--
--   Differences from the source:
--   - generalization: x ∈ 𝓑, the polyhedral feasible set of the chapter → x ∈ B for an arbitrary set B; reason: the claim only compares points with x = x*, so the shape of 𝓑 plays no part; the polyhedral 𝓑 is a special case
--   - encoding: t(ξ), h(ξ) functions of a random vector ξ → maps t, h on the underlying probability space; reason: taking t ∘ ξ and h ∘ ξ recovers the book's form
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, p.163

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_KallMayerSLP_CondExp_IsQuantile
import Definitions.Def_KallMayerSLP_CondExp_cvarObjective
import Definitions.Def_KallMayerSLP_CondExp_cvar
import Definitions.Def_KallMayerSLP_CondExp_wC

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- If `(x*, z*)` solves (4.35), `min_{(x, z), x ∈ B} cᵀx + z + (1 / (1 - α)) 𝔼[(ζ(x, ξ) - z)⁺]`, then
`z*` is an `α`-quantile of `Ψ(x*, ·)`, `v(x*, α) ≤ z*`, and
`v_c(x*, α) = z* + (1 / (1 - α)) 𝔼[(ζ(x*, ξ) - z*)⁺]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, p.163 (PDF 173).

**Formalization Note** `v(x, α)` is `valueAtRisk` of `ζ(x, ·)` ((3.3), p.144) and `v_c(x, α)` is
`cvar` of `ζ(x, ·)` (p.162). -/
theorem eq_4_35_optimal {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : Ω → Fin n → ℝ) (h : Ω → ℝ) (htm : Measurable t)
    (hhm : Measurable h) (ht : ∀ i, Integrable (fun ω => t ω i) μ) (hh : Integrable h μ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (c : Fin n → ℝ) (B : Set (Fin n → ℝ)) (xs : Fin n → ℝ) (zs : ℝ)
    (hxs : xs ∈ B)
    (hopt : IsMinOn (fun p : (Fin n → ℝ) × ℝ => c ⬝ᵥ p.1 + wC μ t h α p.1 p.2)
      {p | p.1 ∈ B} (xs, zs)) :
    IsQuantile μ (fun ω => t ω ⬝ᵥ xs - h ω) α zs ∧
      MultistageStochastic.valueAtRisk μ (fun ω => t ω ⬝ᵥ xs - h ω) α ≤ zs ∧
      cvar μ (fun ω => t ω ⬝ᵥ xs - h ω) α =
        cvarObjective μ (fun ω => t ω ⬝ᵥ xs - h ω) α zs := by sorry

end KallMayerSLP.CondExp
