-- Prove2me | Theorems.Thm_OLPRegret_lemma_1
-- name    : OLPRegret.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:37.938449+00:00
-- url     : https://prove2.me/theorems/6a5bdc9e-47a5-4bfa-96da-d9081c2e9c77
-- title:
--   Lemma 1 with (23) — the Hessian of the limiting dual is positive definite and continuous
-- statement:
--   Under Assumptions 2–6, there is a neighbourhood $U$ of $y_\infty^\beta$ such that for every $y\in U$ and every $b$,
--   $$
--   \partial_y\Lambda_\infty^b(y)=\dot\Lambda_\infty^b(y)=b-\mathrm E(\mathbb 1\{\Delta_1(y)>0\}a_1),\qquad
--   \partial_y\dot\Lambda_\infty^b(y)=\ddot\Lambda_\infty(y)=-\partial_y\mathrm E(\mathbb 1\{\Delta_1(y)>0\}a_1),
--   $$
--   the Hessian $\ddot\Lambda_\infty(y)$ is positive definite, and it is continuous in $y$ on $U$.
--
--   Local strong convexity of the limiting dual is what makes the shadow prices stable.
--
--   Differences from the source:
--   - encoding: "positive definite (and hence full rank)"; "exists and is continuous" → self-adjoint with $v'\ddot\Lambda_\infty(y)v>0$ for $v\ne0$; `HasGradientAt` and `HasFDerivAt`, the second of which gives continuity of the gradient; reason: Lean's spelling of the same claims
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 1, p.20; (23), p.21

import Mathlib
import Definitions.Def_OLPRegret_Assumptions

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 1, p.20, with (23), p.21. Near `y∞ᵝ`, for every `b`, the limiting
dual has gradient (23), that gradient has derivative the Hessian
`Λ̈∞(y) = −∂/∂y E(𝟙{Δ₁(y) > 0}a₁)`, the Hessian is positive definite (self-adjoint with
`v′Λ̈∞(y)v > 0`), and it is continuous in `y`. -/
theorem lemma_1 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ yβ : E m, IsMinimizer (LambdaInf μ β) yβ ∧ (∀ i, 0 < yβ i) ∧ ∃ U ∈ 𝓝 yβ,
      (∀ y ∈ U, ∀ b : E m,
        HasGradientAt (LambdaInf μ b) (LambdaDotInf μ b y) y ∧
        HasFDerivAt (LambdaDotInf μ b) (hessInf μ y) y) ∧
      (∀ y ∈ U, IsSelfAdjoint (hessInf μ y) ∧
        ∀ v : E m, v ≠ 0 → 0 < inner ℝ (hessInf μ y v) v) ∧
      ContinuousOn (hessInf μ) U := by sorry

end OLPRegret
