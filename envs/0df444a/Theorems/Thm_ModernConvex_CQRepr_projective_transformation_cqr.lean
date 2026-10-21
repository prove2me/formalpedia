-- Prove2me | Theorems.Thm_ModernConvex_CQRepr_projective_transformation_cqr
-- name    : ModernConvex.CQRepr.projective_transformation_cqr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:30.088312+00:00
-- url     : https://prove2.me/theorems/e746f2f9-0cf7-4b85-b2cb-8bc3a7dee504
-- title:
--   Proposition 3.3.2 — the projective transformation of a lower semicontinuous CQr function is CQr
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R \cup \{\infty\}$ be a lower semicontinuous function that is CQr:
--   $$\operatorname{Epi}\{f\} \equiv \{(x,t) \mid t \ge f(x)\} = \{(x,t) \mid \exists u : Ax + tp + Bu + b \ge_{\mathbf K} 0\}, \qquad (3.3.17)$$
--   where $\mathbf K$ is a direct product of ice cream cones. Assume that the representation is such that $Bu \ge_{\mathbf K} 0$ implies $Bu = 0$. Then the projective transformation $\widehat f^+$ of $f$ (the function whose epigraph is the closure of $\{(x,t,s) \mid s > 0,\ s^{-1}(x,t) \in \operatorname{Epi}\{f\}\}$) is CQr, namely
--   $$\operatorname{Epi}\{\widehat f^+\} = \{(x,t,s) \mid s \ge 0,\ \exists u : Ax + tp + Bu + sb \ge_{\mathbf K} 0\}.$$
--
--   This is rule K.1, the function counterpart of the conic hull rule; the fractional-quadratic function $x^Tx/s$ is the projective transformation of $x^Tx$.
--
--   **Formalization Note** $f$ is `EReal`-valued and never $-\infty$; lower semicontinuity is Mathlib's, which for such $f$ is the book's sequential definition (p. 96). The book writes the representing set once as $\{(t,x) \mid \dots\}$; the order $(x,t)$ is used throughout. This is the statement as printed; a corrected variant adds $\operatorname{Epi}\{f\} \neq \emptyset$ (finding F1: for $f \equiv +\infty$ the right-hand side contains $(0,0,0)$ while the left-hand side is empty).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 96, Proposition 3.3.2, Eq. (3.3.17)

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

namespace ModernConvex.CQRepr

/-- Ben-Tal–Nemirovski, Proposition 3.3.2, p. 96: let \`f : ℝⁿ → ℝ ∪ {∞}\` be lower semicontinuous
and CQr, \`Epi{f} = {(x, t) | ∃ u : Ax + tp + Bu + b ≥_K 0}\` (3.3.17), with a CQR such that
\`Bu ≥_K 0\` implies \`Bu = 0\`. Then \`Epi{f̂⁺} = {(x, t, s) | s ≥ 0, ∃ u : Ax + tp + Bu + sb ≥_K 0}\`. -/
theorem projective_transformation_cqr {n q : ℕ} (K : IceCreamProduct)
    (A : Matrix K.Idx (Fin n) ℝ) (p : K.Idx → ℝ) (B : Matrix K.Idx (Fin q) ℝ) (b : K.Idx → ℝ)
    (f : (Fin n → ℝ) → EReal) (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hf : ∀ (x : Fin n → ℝ) (t : ℝ),
      f x ≤ (t : EReal) ↔ ∃ u : Fin q → ℝ, A *ᵥ x + t • p + B *ᵥ u + b ∈ K.cone)
    (hB : ∀ u : Fin q → ℝ, B *ᵥ u ∈ K.cone → B *ᵥ u = 0) :
    projectiveEpi f =
      {z : (Fin n → ℝ) × ℝ × ℝ | 0 ≤ z.2.2 ∧
        ∃ u : Fin q → ℝ, A *ᵥ z.1 + z.2.1 • p + B *ᵥ u + z.2.2 • b ∈ K.cone} := by sorry

end ModernConvex.CQRepr
