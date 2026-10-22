-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_recessive_cone_cqr
-- name    : ModernConvex.CQRepr.recessive_cone_cqr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:28.254369+00:00
-- url     : https://prove2.me/theorems/ab3dcc6b-b7e4-4d27-9584-596a42a743fd
-- title:
--   Proposition 3.3.6 — a nonempty CQr set with Bu ∈ K ⇒ Bu = 0 is closed, with recessive cone (3.3.27)
-- statement:
--   Let $X$ be a nonempty CQr set with representation
--   $$X = \{x \in \mathbb R^n \mid \exists u : Ax + Bu + b \ge_{\mathbf K} 0\},$$
--   where $\mathbf K$ is a direct product of ice cream cones, and let the representation be such that $Bu \in \mathbf K$ only if $Bu = 0$. Then $X$ is closed, and the recessive cone $\operatorname{Rec}(X) = \{h : x + th \in X\ \forall(x \in X, t \ge 0)\}$ is CQr:
--   $$\operatorname{Rec}(X) = \{h \mid \exists v : Ah + Bv \ge_{\mathbf K} 0\}. \qquad (3.3.27)$$
--
--   This is rule N of the calculus: the recessive cone is obtained from the representation by dropping the right-hand side $b$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 102, Proposition 3.3.6, Eq. (3.3.27)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Proposition 3.3.6, p. 102: let `X = {x ∈ ℝⁿ | ∃ u : Ax + Bu + b ≥_K 0}` be
nonempty, with a CQR such that `Bu ∈ K` only if `Bu = 0`. Then `X` is closed and
`Rec(X) = {h | ∃ v : Ah + Bv ≥_K 0}` (3.3.27). -/
theorem recessive_cone_cqr {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (X : Set (Fin n → ℝ))
    (hX : X = cqrSet K A B b) (hne : X.Nonempty)
    (hB : ∀ u : Fin p → ℝ, B *ᵥ u ∈ K.cone → B *ᵥ u = 0) :
    IsClosed X ∧ recessiveCone X = {h | ∃ v : Fin p → ℝ, A *ᵥ h + B *ᵥ v ∈ K.cone} := by sorry

end ModernConvex.CQRepr
