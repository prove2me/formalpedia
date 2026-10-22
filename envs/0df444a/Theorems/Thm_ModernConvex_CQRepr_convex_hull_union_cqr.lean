-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_convex_hull_union_cqr
-- name    : ModernConvex.CQRepr.convex_hull_union_cqr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:34.155078+00:00
-- url     : https://prove2.me/theorems/04818c32-93e1-4be6-85d5-4f38071295c7
-- title:
--   Proposition 3.3.5 (Nesterov) — the CQr set (3.3.23) lies between the convex hull and the closed convex hull of X₁ ∪ ⋯ ∪ X_k
-- statement:
--   Let $X_1, \dots, X_k \subset \mathbb R^n$ be nonempty convex CQr sets,
--   $$X_i = \{x \mid \exists u_i : A_ix + B_iu_i + b_i \ge_{\mathbf K_i} 0\}, \quad i = 1, \dots, k, \qquad (3.3.22)$$
--   where each $\mathbf K_i$ is a direct product of ice cream cones. Let
--   $$Y = \Bigl\{x \;\Bigm|\; \exists \xi^1,\dots,\xi^k, t_1,\dots,t_k, \eta^1,\dots,\eta^k :\ A_i\xi^i + B_i\eta^i + t_ib_i \ge_{\mathbf K_i} 0\ (i = 1,\dots,k),\ t_1,\dots,t_k \ge 0,\ \xi^1 + \cdots + \xi^k = x,\ t_1 + \cdots + t_k = 1\Bigr\} \qquad (3.3.23)$$
--   (the $k$ block inequalities together are one inequality $\ge_{\mathbf K} 0$ with $\mathbf K = \mathbf K_1 \times \cdots \times \mathbf K_k$). Then:
--
--   1. $Y$ lies between the convex hull and the closed convex hull of the union:
--   $$\operatorname{Conv}\Bigl(\bigcup_{i=1}^k X_i\Bigr) \subset Y \subset \operatorname{cl}\operatorname{Conv}\Bigl(\bigcup_{i=1}^k X_i\Bigr).$$
--   2. If, in addition, (i) all $X_i$ are closed and bounded, or (ii) $X_i = Z_i + W$ for all $i$, where the $Z_i$ are closed and bounded sets and $W$ is a convex closed set, then
--   $$\operatorname{Conv}\Bigl(\bigcup_{i=1}^k X_i\Bigr) = Y = \operatorname{cl}\operatorname{Conv}\Bigl(\bigcup_{i=1}^k X_i\Bigr)$$
--   and this set is CQr.
--
--   This is rule M of the calculus of CQ-representability, due to Nesterov: the convex hull of finitely many CQr sets is "nearly" CQr, with an explicit representation whose size is the sum of the sizes of the given ones. It is what makes disjunctions of conic quadratic sets tractable.
--
--   **Formalization Note** $\operatorname{Conv}$ is Mathlib's `convexHull ℝ`, and the closed convex hull is its topological closure (the book's overlined Conv). The page writes (3.3.22) without the quantifier "$\exists u_i$"; the intended projection is formalized. "$\operatorname{Conv}(\bigcup X_i)$ is CQr" uses the definition of p. 86 in $\mathbb R^n$. The convexity of the $X_i$ is a hypothesis as on the page, although CQr sets are convex anyway. For $k = 0$ every set involved is empty.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 99–100, Proposition 3.3.5, Eqs. (3.3.22)–(3.3.23)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

open Pointwise

/-- Ben-Tal–Nemirovski, Proposition 3.3.5, pp. 99–100 (Nesterov): let `X₁, …, X_k ⊂ ℝⁿ` be
nonempty convex CQr sets, `Xᵢ = {x | ∃ uᵢ : Aᵢx + Bᵢuᵢ + bᵢ ≥_{Kᵢ} 0}` (3.3.22), each `Kᵢ` a direct
product of ice cream cones. Then the set `Y` of (3.3.23) satisfies
`Conv(⋃ Xᵢ) ⊂ Y ⊂ cl Conv(⋃ Xᵢ)`; and if (i) all `Xᵢ` are closed and bounded, or (ii)
`Xᵢ = Zᵢ + W` with `Zᵢ` closed and bounded and `W` convex and closed, then
`Conv(⋃ Xᵢ) = Y = cl Conv(⋃ Xᵢ)` is CQr. -/
theorem convex_hull_union_cqr {n k : ℕ} (K : Fin k → IceCreamProduct) (p : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (K i).Idx (Fin n) ℝ) (B : (i : Fin k) → Matrix (K i).Idx (Fin (p i)) ℝ)
    (b : (i : Fin k) → (K i).Idx → ℝ) (X : Fin k → Set (Fin n → ℝ))
    (hX : ∀ i, X i = cqrSet (K i) (A i) (B i) (b i))
    (hne : ∀ i, (X i).Nonempty) (hconv : ∀ i, Convex ℝ (X i)) :
    let Y : Set (Fin n → ℝ) :=
      {x | ∃ (ξ : Fin k → Fin n → ℝ) (t : Fin k → ℝ) (η : (i : Fin k) → Fin (p i) → ℝ),
        (∀ i, A i *ᵥ ξ i + B i *ᵥ η i + t i • b i ∈ (K i).cone) ∧
        (∀ i, 0 ≤ t i) ∧ ∑ i, ξ i = x ∧ ∑ i, t i = 1}
    (convexHull ℝ (⋃ i, X i) ⊆ Y ∧ Y ⊆ closure (convexHull ℝ (⋃ i, X i))) ∧
      (((∀ i, IsClosed (X i) ∧ Bornology.IsBounded (X i)) ∨
          (∃ (Z : Fin k → Set (Fin n → ℝ)) (W : Set (Fin n → ℝ)),
            (∀ i, IsClosed (Z i) ∧ Bornology.IsBounded (Z i)) ∧ Convex ℝ W ∧ IsClosed W ∧
              ∀ i, X i = Z i + W)) →
        convexHull ℝ (⋃ i, X i) = Y ∧ Y = closure (convexHull ℝ (⋃ i, X i)) ∧
          IsCQr (convexHull ℝ (⋃ i, X i))) := by sorry

end ModernConvex.CQRepr
