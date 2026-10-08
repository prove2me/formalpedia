-- Prove2me | Theorems.Thm_OTDRO_Cvx_ellRob_convex
-- name    : OTDRO.Cvx.ellRob_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:20.248695+00:00
-- url     : https://prove2.me/theorems/5bfff097-a14a-4580-a736-4b996360423d
-- title:
--   Lemma 2, p. 16 — (β, λ) ↦ ℓ_rob(β, λ; x) is convex on B × ℝ₊ for every x
-- statement:
--   Let $A : \mathbb{R}^d \to \mathbb{R}^{d\times d}$ take positive definite values with lower semicontinuous cost $c(x, x') = (x - x')^{\mathsf T}A(x)(x - x')$ (Assumption 1a), let $\ell : \mathbb{R} \to \mathbb{R}$ be convex, $\delta > 0$, and let $B \subseteq \mathbb{R}^d$ be convex. Then for every $x \in \mathbb{R}^d$ the map $(\beta, \lambda) \mapsto \ell_{rob}(\beta, \lambda; x)$ is convex on $B \times \mathbb{R}_+$: for $(\beta_1, \lambda_1), (\beta_2, \lambda_2) \in B \times \mathbb{R}_+$ and $\alpha \in [0, 1]$,
--   $$\ell_{rob}\big(\alpha\beta_1 + (1-\alpha)\beta_2,\ \alpha\lambda_1 + (1-\alpha)\lambda_2;\ x\big) \le \alpha\,\ell_{rob}(\beta_1, \lambda_1; x) + (1-\alpha)\,\ell_{rob}(\beta_2, \lambda_2; x).$$
--
--   Pointwise convexity of the robust loss is the step from which convexity of the dual objective $f_\delta$ follows by integration.
--
--   **Formalization Note** $\ell_{rob}$ takes values in $(-\infty, +\infty]$, so convexity is written as the displayed inequality in `EReal` rather than with `ConvexOn`; with Mathlib's convention $0 \cdot (+\infty) = 0$ the inequality reduces to an equality at $\alpha \in \{0, 1\}$. The paper assumes "Assumptions 1a and 2"; only the convexity of $\ell$ from Assumption 2 is kept, and Assumption 1(b) is not assumed, which makes the statement stronger. No probability measure appears.
-- source:
--   arXiv:1810.02403v3, Lemma 2, p. 16 (proof in §5.1, p. 32)

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Cvx

open Matrix

/-- **Lemma 2**, p. 16: under Assumption 1a (`A(x)` positive definite for every `x`, the cost
lower semicontinuous) and the convexity of `ℓ` from Assumption 2, the map
`(β, λ) ↦ ℓ_rob(β, λ; x)` is convex on `B × ℝ₊` for every `x ∈ ℝ^d`. Convexity of the
`EReal`-valued map is written out: for `θᵢ = (βᵢ, λᵢ) ∈ B × ℝ₊` and `α ∈ [0, 1]`,
`ℓ_rob(αθ₁ + (1 − α)θ₂; x) ≤ α ℓ_rob(θ₁; x) + (1 − α) ℓ_rob(θ₂; x)`. -/
theorem ellRob_convex {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hPD : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2))
    (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ) (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ β₁ ∈ B, ∀ β₂ ∈ B, ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        OTDRO.Dual.ellRob ℓ A δ (α • β₁ + (1 - α) • β₂) (α * lam₁ + (1 - α) * lam₂) x ≤
          (α : EReal) * OTDRO.Dual.ellRob ℓ A δ β₁ lam₁ x +
            ((1 - α : ℝ) : EReal) * OTDRO.Dual.ellRob ℓ A δ β₂ lam₂ x := by sorry

end OTDRO.Cvx
