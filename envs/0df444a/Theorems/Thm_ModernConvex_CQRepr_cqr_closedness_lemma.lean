-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_cqr_closedness_lemma
-- name    : ModernConvex.CQRepr.cqr_closedness_lemma
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:29.809483+00:00
-- url     : https://prove2.me/theorems/a4162618-b3e7-48d6-a911-28d79d51cab3
-- title:
--   Lemma 3.3.1 — if Qv ∈ K only when Qv = 0, then ‖Qv‖₂ is bounded as in (3.3.13) and Y is closed
-- statement:
--   Let $\mathbf K$ be a direct product of ice cream cones and let $Y \subset \mathbb R^n$ be a CQr set with representation
--   $$Y = \{y \mid \exists v : Py + Qv + r \ge_{\mathbf K} 0\}$$
--   such that $Qv \in \mathbf K$ only when $Qv = 0$. Then:
--
--   1. there is a constant $C < \infty$ such that for all $y, v$,
--   $$Py + Qv + r \in \mathbf K \;\Longrightarrow\; \|Qv\|_2 \le C\,(1 + \|Py + r\|_2); \qquad (3.3.13)$$
--   2. $Y$ is closed.
--
--   The lemma is the closedness tool behind the conic hull and recessive cone rules of §3.3: the projection of a closed set need not be closed, and the condition on $Q$ is what rules this out.
--
--   **Formalization Note** $\|\cdot\|_2$ is the Euclidean norm, written out explicitly. The constant $C$ may depend on $P, Q, r$ and $\mathbf K$, as on the page.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 95, Lemma 3.3.1, Eq. (3.3.13)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Lemma 3.3.1, p. 95: let `Y = {y | ∃ v : Py + Qv + r ≥_K 0}` be a CQR such
that `Qv ∈ K` only when `Qv = 0`. Then (i) there is a constant `C < ∞` with
`Py + Qv + r ∈ K ⇒ ‖Qv‖₂ ≤ C(1 + ‖Py + r‖₂)` (3.3.13), and (ii) `Y` is closed. -/
theorem cqr_closedness_lemma {n p : ℕ} (K : IceCreamProduct) (P : Matrix K.Idx (Fin n) ℝ)
    (Q : Matrix K.Idx (Fin p) ℝ) (r : K.Idx → ℝ)
    (hQ : ∀ v : Fin p → ℝ, Q *ᵥ v ∈ K.cone → Q *ᵥ v = 0) :
    (∃ C : ℝ, ∀ (y : Fin n → ℝ) (v : Fin p → ℝ), P *ᵥ y + Q *ᵥ v + r ∈ K.cone →
        eucNorm (Q *ᵥ v) ≤ C * (1 + eucNorm (P *ᵥ y + r))) ∧
      IsClosed (cqrSet K P Q r) := by sorry

end ModernConvex.CQRepr
