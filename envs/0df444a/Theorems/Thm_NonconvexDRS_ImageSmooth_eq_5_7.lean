-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_eq_5_7
-- name    : NonconvexDRS.ImageSmooth.eq_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:41.881493+00:00
-- url     : https://prove2.me/theorems/d4181001-c07e-4f35-98e0-d1e30530a4c4
-- title:
--   (5.7), proof of Theorem 5.13, p. 25 — Aᵀyᵢ = ∇f(xᵢ) for some xᵢ ∈ X(sᵢ), and ⟨y₁ − y₂, s₁ − s₂⟩ = ⟨∇f(x₁) − ∇f(x₂), x₁ − x₂⟩
-- statement:
--   Let $A\in\mathbb R^{p\times n}$ be surjective and $f:\mathbb R^n\to\mathbb R$ lower semicontinuous and continuously differentiable, and suppose there is $\beta\ge0$ such that $x\mapsto f(x)+\frac\beta2\|Ax-s\|^2$ is level bounded for every $s\in\mathbb R^p$. Let $s_1,s_2\in\mathbb R^p$ and let $y_i\in\partial(Af)(s_i)$, $i=1,2$, be limiting subgradients of the image function. Then there are minimizers $x_i\in X(s_i)=\operatorname*{arg\,min}\{f(x)\mid Ax=s_i\}$ with $A^\top y_i=\nabla f(x_i)$, $i=1,2$, and for them
--   $$\langle y_1-y_2,s_1-s_2\rangle=\langle\nabla f(x_1)-\nabla f(x_2),x_1-x_2\rangle.\qquad(5.7)$$
--
--   Identity (5.7) turns any monotonicity bound on $\nabla f$ along the minimizers into the bound (2.4) for the subgradients of $(Af)$, which is how each case of Theorem 5.13 is concluded through Lemma 2.1.
--
--   **Formalization Note** The page derives $A^\top y_i\in\partial f(x_i)$ from Proposition 5.3, which concerns regular subgradients, while $y_i$ is a limiting subgradient; the passage to limits uses the uniform level boundedness of the proof. The statement is made for the limiting subdifferential (the published `NonconvexSplitting.Shared.LimitingSubdiff`), as the proof needs it. Continuous differentiability is the page's hypothesis for this step ("continuous differentiability of $f$").
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 25, (5.7), proof of Theorem 5.13

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proof of Theorem 5.13, (5.7), p. 25: under the hypotheses of Theorem 5.13 and for continuously
differentiable `f`, for all `sᵢ` and all limiting subgradients `yᵢ ∈ ∂(Af)(sᵢ)`, `i = 1, 2`, there are
`xᵢ ∈ X(sᵢ) = argmin {f(x) | Ax = sᵢ}` with `Aᵀyᵢ = ∇f(xᵢ)`, and then
`⟨y₁ - y₂, s₁ - s₂⟩ = ⟨∇f(x₁) - ∇f(x₂), x₁ - x₂⟩`. -/
theorem eq_5_7 {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (hC1 : ContDiff ℝ 1 f) :
    ∀ (s₁ s₂ y₁ y₂ : EuclideanSpace ℝ (Fin p)),
      y₁ ∈ LimitingSubdiff (imageFn A (fun x => (f x : EReal))) s₁ →
      y₂ ∈ LimitingSubdiff (imageFn A (fun x => (f x : EReal))) s₂ →
      ∃ x₁ x₂ : EuclideanSpace ℝ (Fin n),
        (A x₁ = s₁ ∧ ∀ x', A x' = s₁ → f x₁ ≤ f x') ∧
        (A x₂ = s₂ ∧ ∀ x', A x' = s₂ → f x₂ ≤ f x') ∧
        ContinuousLinearMap.adjoint A y₁ = gradient f x₁ ∧
        ContinuousLinearMap.adjoint A y₂ = gradient f x₂ ∧
        ⟪y₁ - y₂, s₁ - s₂⟫_ℝ = ⟪gradient f x₁ - gradient f x₂, x₁ - x₂⟫_ℝ := by sorry

end NonconvexDRS.ImageSmooth
