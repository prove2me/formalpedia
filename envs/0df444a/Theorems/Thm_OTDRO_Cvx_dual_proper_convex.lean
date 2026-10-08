-- Prove2me | Theorems.Thm_OTDRO_Cvx_dual_proper_convex
-- name    : OTDRO.Cvx.dual_proper_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:28.750267+00:00
-- url     : https://prove2.me/theorems/fd1e3ad3-d8db-41da-9f70-ed74faa2ac28
-- title:
--   Theorem 2, p. 10 — f_δ : B × ℝ₊ → ℝ ∪ {∞} is proper and convex under Assumptions 1 and 2
-- statement:
--   Let $P_0$ be a Borel probability measure on $\mathbb{R}^d$, let $A$ satisfy Assumption 1 and $\ell$ and $P_0$ satisfy Assumption 2, let $\delta > 0$ and let the decision set $B \subseteq \mathbb{R}^d$ be convex. Consider the dual objective
--   $$f_\delta(\beta, \lambda) = E_{P_0}\big[\ell_{rob}(\beta, \lambda; X)\big], \qquad (\beta, \lambda) \in B \times \mathbb{R}_+,$$
--   with values in $\mathbb{R} \cup \{\infty\}$. Then $f_\delta$ is proper and convex:
--
--   1. $f_\delta(\beta, \lambda) > -\infty$ for every $(\beta, \lambda) \in B \times \mathbb{R}_+$;
--   2. for every $\beta \in B$ there is $\lambda \ge 0$ with $f_\delta(\beta, \lambda) < +\infty$;
--   3. for $(\beta_1, \lambda_1), (\beta_2, \lambda_2) \in B \times \mathbb{R}_+$ and $\alpha \in [0, 1]$,
--   $$f_\delta\big(\alpha\beta_1 + (1-\alpha)\beta_2,\ \alpha\lambda_1 + (1-\alpha)\lambda_2\big) \le \alpha f_\delta(\beta_1, \lambda_1) + (1-\alpha) f_\delta(\beta_2, \lambda_2).$$
--
--   By Theorem 1 of the paper, the distributionally robust objective $\sup_{P : D_c(P_0, P) \le \delta} E_P[\ell(\beta^{\mathsf T}X)]$ equals $\inf_{\lambda \ge 0} f_\delta(\beta, \lambda)$, so the robust problem becomes a joint convex minimization of $f_\delta$ over $(\beta, \lambda)$; this is the basis of the paper's stochastic gradient schemes.
--
--   **Formalization Note** $f_\delta$ is the `EReal`-valued integral $\int \ell_{rob}^+ \, dP_0 - \int \ell_{rob}^- \, dP_0$. Convexity is the displayed inequality in `EReal` (with $0 \cdot (+\infty) = 0$), since `ConvexOn` does not apply to `EReal`-valued maps; together with item 1 the right-hand side never involves $-\infty + \infty$. "Proper" is item 1 together with item 2; item 2 is stated for each $\beta \in B$, which is stronger than "finite at some point of $B \times \mathbb{R}_+$" whenever $B \neq \emptyset$ and avoids a nonemptiness hypothesis on $B$ (for $B = \emptyset$ the statement is vacuous). The convexity of $B$ is the paper's standing assumption (p. 1); $\delta > 0$ is the paper's standing assumption on the budget.
-- source:
--   arXiv:1810.02403v3, Theorem 2, p. 10 (proof in §5.1, p. 33)

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Cvx

open MeasureTheory

/-- **Theorem 2**, p. 10: under Assumptions 1 and 2, the dual objective
`f_δ(β, λ) = E_{P₀}[ℓ_rob(β, λ; X)]`, a map `B × ℝ₊ → ℝ ∪ {∞}`, is proper and convex:
1. it never takes the value `−∞` on `B × ℝ₊`;
2. for every `β ∈ B` it is finite at some `λ ≥ 0`;
3. for `(βᵢ, λᵢ) ∈ B × ℝ₊` and `α ∈ [0, 1]`,
   `f_δ(αβ₁ + (1 − α)β₂, αλ₁ + (1 − α)λ₂) ≤ α f_δ(β₁, λ₁) + (1 − α) f_δ(β₂, λ₂)`. -/
theorem dual_proper_convex {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ) :
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊥) ∧
    (∀ β ∈ B, ∃ lam : ℝ, 0 ≤ lam ∧ OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊤) ∧
    (∀ β₁ ∈ B, ∀ β₂ ∈ B, ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        OTDRO.Dual.fDelta P0 ℓ A δ (α • β₁ + (1 - α) • β₂) (α * lam₁ + (1 - α) * lam₂) ≤
          (α : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β₁ lam₁ +
            ((1 - α : ℝ) : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β₂ lam₂) := by sorry

end OTDRO.Cvx
