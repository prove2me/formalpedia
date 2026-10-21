-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_legendre_cqr
-- name    : ModernConvex.CQRepr.legendre_cqr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:35.104125+00:00
-- url     : https://prove2.me/theorems/c8097da2-a904-4a9e-ba5f-a0fce912b6c5
-- title:
--   Proposition 3.3.4 — the Legendre transformation of a CQr function with a strictly feasible CQR is CQr, (3.3.20)
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R \cup \{\infty\}$ be CQr,
--   $$\{(x,t) \mid t \ge f(x)\} = \{(x,t) \mid \exists u : Ax + tp + Bu + b \ge_{\mathbf K} 0\},$$
--   where $\mathbf K$ is a direct product of ice cream cones, and assume the representation is strictly feasible: $A\bar x + \bar t p + B\bar u + b >_{\mathbf K} 0$ for some $\bar x, \bar t, \bar u$. Then the Legendre transformation $f_*(y) = \sup_x[y^Tx - f(x)]$ is CQr:
--   $$\operatorname{Epi}\{f_*\} = \{(y,s) \mid \exists \xi : A^T\xi = -y,\ B^T\xi = 0,\ p^T\xi = 1,\ s \ge b^T\xi,\ \xi \ge_{\mathbf K} 0\}. \qquad (3.3.20)$$
--
--   This is rule L.1, the function counterpart of the polar rule; with it, conjugates of CQr functions can be used inside conic quadratic models.
--
--   **Formalization Note** $f$ is `EReal`-valued and never $-\infty$; $f_*$ is computed in `EReal` (so $y^Tx - (+\infty) = -\infty$), and $(y,s) \in \operatorname{Epi}\{f_*\}$ means $f_*(y) \le s$ for real $s$. The book writes the representing set as $\{(t,x) \mid \dots\}$; the order $(x,t)$ is used. $>_{\mathbf K} 0$ is membership in the interior of $\mathbf K$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 98, Proposition 3.3.4, Eq. (3.3.20)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Proposition 3.3.4, p. 98: let `f : ℝⁿ → ℝ ∪ {∞}` be CQr,
`{(x, t) | t ≥ f(x)} = {(x, t) | ∃ u : Ax + tp + Bu + b ≥_K 0}`, with a strictly feasible CQR
(`Ax̄ + t̄p + Bū + b >_K 0`). Then
`Epi{f∗} = {(y, s) | ∃ ξ : Aᵀξ = −y, Bᵀξ = 0, pᵀξ = 1, s ≥ bᵀξ, ξ ≥_K 0}` (3.3.20). -/
theorem legendre_cqr {n q : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (p : K.Idx → ℝ) (B : Matrix K.Idx (Fin q) ℝ) (b : K.Idx → ℝ)
    (f : (Fin n → ℝ) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hf : ∀ (x : Fin n → ℝ) (t : ℝ),
      f x ≤ (t : EReal) ↔ ∃ u : Fin q → ℝ, A *ᵥ x + t • p + B *ᵥ u + b ∈ K.cone)
    (hstrict : ∃ (x : Fin n → ℝ) (t : ℝ) (u : Fin q → ℝ),
      A *ᵥ x + t • p + B *ᵥ u + b ∈ interior K.cone) :
    ∀ (y : Fin n → ℝ) (s : ℝ), legendre f y ≤ (s : EReal) ↔
      ∃ ξ : K.Idx → ℝ, Aᵀ *ᵥ ξ = -y ∧ Bᵀ *ᵥ ξ = 0 ∧ p ⬝ᵥ ξ = 1 ∧ b ⬝ᵥ ξ ≤ s ∧ ξ ∈ K.cone := by sorry

end ModernConvex.CQRepr
