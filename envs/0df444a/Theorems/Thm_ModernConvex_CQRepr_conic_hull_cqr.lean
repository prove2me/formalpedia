-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_conic_hull_cqr
-- name    : ModernConvex.CQRepr.conic_hull_cqr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:25.429468+00:00
-- url     : https://prove2.me/theorems/d01bd424-e0b8-4183-9129-e2ed8375866d
-- title:
--   Proposition 3.3.1 — the CQr set (3.3.12) lies between the conic hull and the closed conic hull
-- statement:
--   Let $X \subset \mathbb R^n$ be a nonempty CQr set,
--   $$X = \{x \mid \exists u : Ax + Bu + b \ge_{\mathbf K} 0\}, \qquad (3.3.11)$$
--   where $\mathbf K$ is a direct product of ice cream cones, and let
--   $$\widetilde X^+ = \{(x,t) \mid \exists u : Ax + Bu + tb \ge_{\mathbf K} 0\} \cap \{(x,t) \mid t \ge 0\}. \qquad (3.3.12)$$
--   Write $X^+ = \{(x,t) : t > 0,\ t^{-1}x \in X\} \cup \{0\}$ for the conic hull of $X$ and $\widehat X^+ = \operatorname{cl} X^+$ for its closed conic hull. Then:
--
--   1. $X^+ \subset \widetilde X^+ \subset \widehat X^+$; in particular, if $X$ is closed and bounded, the conic hull $X^+$ is CQr.
--   2. If the representation (3.3.11) is such that $Bu \in \mathbf K$ implies $Bu = 0$, then $\widetilde X^+ = \widehat X^+$, so that $\widehat X^+$ is CQr.
--
--   This is rule K of the calculus of CQ-representability: the conic hull of a CQr set is "nearly" CQr, with an explicit representation obtained by homogenizing the right-hand side $b$.
--
--   **Formalization Note** A pair $(x,t) \in \mathbb R^n \times \mathbb R$ is a vector of $\mathbb R^{n+1}$ with last coordinate $t$. "Is CQr" for subsets of $\mathbb R^{n+1}$ is the definition of p. 86 in dimension $n+1$. The hypothesis "$X$ nonempty" of part (i) is kept for part (ii), which refers to the same representation (3.3.11); without it (ii) fails (e.g. $A = 0$ with a right-hand side $b$ that makes $X$ empty).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 94, Proposition 3.3.1, Eqs. (3.3.11)–(3.3.12)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Proposition 3.3.1, p. 94. Let `X = {x | ∃ u : Ax + Bu + b ≥_K 0}` (3.3.11)
be nonempty, `K` a direct product of ice cream cones, and let
`X̃⁺ = {(x, t) | ∃ u : Ax + Bu + tb ≥_K 0} ∩ {(x, t) | t ≥ 0}` (3.3.12), points `(x, t)` of
`ℝⁿ × ℝ` being vectors `z ∈ ℝⁿ⁺¹` with `x = Fin.init z`, `t = z (Fin.last n)`.
(i) `X⁺ ⊂ X̃⁺ ⊂ cl X⁺`; in particular, if `X` is closed and bounded, the conic hull `X⁺` is CQr.
(ii) If `Bu ∈ K` implies `Bu = 0`, then `X̃⁺ = cl X⁺`, so that `cl X⁺` is CQr. -/
theorem conic_hull_cqr {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (X : Set (Fin n → ℝ))
    (hX : X = cqrSet K A B b) (hne : X.Nonempty) :
    let Xt : Set (Fin (n + 1) → ℝ) :=
      {z | (∃ u : Fin p → ℝ, A *ᵥ Fin.init z + B *ᵥ u + z (Fin.last n) • b ∈ K.cone) ∧
        0 ≤ z (Fin.last n)}
    (conicHull X ⊆ Xt ∧ Xt ⊆ closure (conicHull X) ∧
        (IsClosed X → Bornology.IsBounded X → IsCQr (conicHull X))) ∧
      ((∀ u : Fin p → ℝ, B *ᵥ u ∈ K.cone → B *ᵥ u = 0) →
        Xt = closure (conicHull X) ∧ IsCQr (closure (conicHull X))) := by sorry

end ModernConvex.CQRepr
