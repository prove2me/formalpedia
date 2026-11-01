-- Prove2me | Theorems.Thm_FracMPGA_proposition_2_1_ii
-- name    : FracMPGA.proposition_2_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:57.697989+00:00
-- url     : https://prove2.me/theorems/ab0501d9-97fc-491f-9939-a2878085cb18
-- title:
--   Proposition 2.1 (ii) — Fréchet subdifferential of the lifted ratio $\rho$ (from [21, Proposition 2.3])
-- statement:
--   Let $\varphi_1:\mathbb R^n\to(-\infty,+\infty]$, $\varphi_2:\mathbb R^n\to\mathbb R$, and let $\rho(x,y)=\varphi_1(x)/(\langle x,y\rangle-\varphi_2^*(y))$ be the lifted ratio. Let $(x,y)\in\operatorname{dom}\varphi_1\times\operatorname{dom}\varphi_2^*$, $a_1=\varphi_1(x)$ and $a_3=\langle x,y\rangle-\varphi_2^*(y)$, and suppose $\varphi_1$ is continuous at $x$ relative to $\operatorname{dom}\varphi_1$. If $a_1>0$, $a_3>0$ and $\varphi_2^*$ satisfies the calmness condition at $y$ relative to $\operatorname{dom}\varphi_2^*$, then
--   $$
--   \hat\partial\rho(x,y)=\frac{a_3\hat\partial\varphi_1(x)-a_1y}{a_3^2}\times\frac{\hat\partial(a_1\varphi_2^*)(y)-a_1x}{a_3^2}.
--   $$
--
--   The paper quotes this quotient rule from [21] and uses it to produce the subgradients of $Q$ in Proposition 6.3.
--
--   **Formalization Note** $\hat\partial$ is the Fréchet subdifferential on the Euclidean product, and the right-hand side is the product of the two displayed sets. Item (i) of Proposition 2.1, about the other ratio $\tau$ and cited from [43], is a separate result and is not part of this item.
--
--   Differences from the source:
--   - encoding: ℝⁿ × ℝⁿ with the Euclidean norm → Pair n = WithLp 2 (Vec n × Vec n); reason: Lean convention; the same norm
--   - encoding: φ₁ : ℝⁿ → (−∞, +∞], φ₂ with dom(φ₂) = ℝⁿ → φ₁ : Vec n → EReal with φ₁ ≠ ⊥ everywhere, φ₂ : Vec n → ℝ; reason: the same functions
--   - encoding: a₂ = φ₂(x) in the preamble → omitted; reason: a₂ enters only item (i)
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §2.1, p.6, Proposition 2.1 (ii) (cited from [21, Proposition 2.3])

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracMPGA_IsCalmOn
import Definitions.Def_FracMPGA_liftedRatio
open NonconvexSplitting.Shared

namespace FracMPGA

/-- **Proposition 2.1 (ii)** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.6 (cited there from [21,
Proposition 2.3]): let `φ₁ : ℝⁿ → (−∞, +∞]`, `φ₂ : ℝⁿ → ℝ` (`dom(φ₂) = ℝⁿ`), `ρ` the lifted ratio
of p.6, `(x, y) ∈ dom(φ₁) × dom(φ₂*)`, `a₁ = φ₁(x)` and `a₃ = ⟨x, y⟩ − φ₂*(y)`. Suppose that `φ₁`
is continuous at `x` relative to `dom(φ₁)`. If `a₁ > 0`, `a₃ > 0` and `φ₂*` satisfies the calmness
condition at `y` relative to `dom(φ₂*)`, then
`∂̂ρ(x, y) = (a₃∂̂φ₁(x) − a₁y)/a₃² × (∂̂(a₁φ₂*)(y) − a₁x)/a₃²`.

**Formalization Note** `∂̂` is the Fréchet subdifferential `IsRegularSubgrad`; `ρ` is a function
on the Euclidean product `ℝⁿ × ℝⁿ` (`liftedRatioPair`), so `∂̂ρ(x, y)` is a set of pairs and the
right-hand side is the product of the two displayed sets. `a₁φ₂*` is `z ↦ (a₁ : EReal) * φ₂*(z)`.
The page's `a₂ = φ₂(x)` enters only item (i) and is omitted. -/
theorem proposition_2_1_ii {n : ℕ} (φ₁ : Vec n → EReal) (φ₂ : Vec n → ℝ)
    (hφ₁ : ∀ z, φ₁ z ≠ ⊥) (x y : Vec n) (hx : φ₁ x ≠ ⊤)
    (hy : ConvexOptimization.fenchelConjugate φ₂ y ≠ ⊤)
    (hcont : ContinuousWithinAt φ₁ {z | φ₁ z ≠ ⊤} x)
    (ha₁ : 0 < (φ₁ x).toReal) (ha₃ : 0 < (liftDen φ₂ x y).toReal)
    (hcalm : IsCalmAt (ConvexOptimization.fenchelConjugate φ₂) y
      {z | ConvexOptimization.fenchelConjugate φ₂ z ≠ ⊤}) :
    {w : Pair n | IsRegularSubgrad (liftedRatioPair φ₁ φ₂) (pair x y) w} =
      {w : Pair n |
        (∃ u : Vec n, IsRegularSubgrad φ₁ x u ∧
          w.ofLp.1 = ((liftDen φ₂ x y).toReal ^ 2)⁻¹ •
            ((liftDen φ₂ x y).toReal • u - (φ₁ x).toReal • y)) ∧
        (∃ v : Vec n,
          IsRegularSubgrad (fun z => (((φ₁ x).toReal : ℝ) : EReal) *
            ConvexOptimization.fenchelConjugate φ₂ z) y v ∧
          w.ofLp.2 = ((liftDen φ₂ x y).toReal ^ 2)⁻¹ • (v - (φ₁ x).toReal • x))} := by sorry

end FracMPGA
