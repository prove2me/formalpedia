-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_polar_cqr
-- name    : ModernConvex.CQRepr.polar_cqr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:33.112145+00:00
-- url     : https://prove2.me/theorems/7ee6cc84-6369-4204-a9d9-a31f57c0b414
-- title:
--   Proposition 3.3.3 — the polar of a CQr set with a strictly feasible CQR is the CQr set (3.3.19)
-- statement:
--   Let $X \subset \mathbb R^n$ with $0 \in X$ be a CQr set,
--   $$X = \{x \mid \exists u : Ax + Bu + b \ge_{\mathbf K} 0\}, \qquad (3.3.18)$$
--   where $\mathbf K$ is a direct product of ice cream cones, and assume the representation is strictly feasible: $A\bar x + B\bar u + b >_{\mathbf K} 0$ for some $\bar x, \bar u$. Then the polar $X_* = \{y \mid y^Tx \le 1\ \forall x \in X\}$ is the CQr set
--   $$X_* = \{y \mid \exists \xi : A^T\xi + y = 0,\ B^T\xi = 0,\ b^T\xi \le 1,\ \xi \ge_{\mathbf K} 0\}. \qquad (3.3.19)$$
--
--   This is rule L: polarity nearly preserves CQ-representability, with an explicit representation through the self-dual cone $\mathbf K$.
--
--   **Formalization Note** $>_{\mathbf K} 0$ is membership in the topological interior of $\mathbf K$. No Assumption A is imposed on the representation (footnote 12, p. 86).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 97, Proposition 3.3.3, Eqs. (3.3.18)–(3.3.19)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Proposition 3.3.3, p. 97: let `X ⊂ ℝⁿ`, `0 ∈ X`, be CQr,
`X = {x | ∃ u : Ax + Bu + b ≥_K 0}` (3.3.18), with a strictly feasible CQR
(`Ax̄ + Bū + b >_K 0` for some `x̄, ū`). Then
`X∗ = {y | ∃ ξ : Aᵀξ + y = 0, Bᵀξ = 0, bᵀξ ≤ 1, ξ ≥_K 0}` (3.3.19). -/
theorem polar_cqr {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (X : Set (Fin n → ℝ))
    (h0 : (0 : Fin n → ℝ) ∈ X) (hX : X = cqrSet K A B b)
    (hstrict : ∃ (x : Fin n → ℝ) (u : Fin p → ℝ), A *ᵥ x + B *ᵥ u + b ∈ interior K.cone) :
    polar X = {y | ∃ ξ : K.Idx → ℝ, Aᵀ *ᵥ ξ + y = 0 ∧ Bᵀ *ᵥ ξ = 0 ∧ b ⬝ᵥ ξ ≤ 1 ∧ ξ ∈ K.cone} := by sorry

end ModernConvex.CQRepr
