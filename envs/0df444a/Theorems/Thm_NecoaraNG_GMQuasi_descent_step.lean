-- Prove2me | Theorems.Thm_NecoaraNG_GMQuasi_descent_step
-- name    : NecoaraNG.GMQuasi.descent_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:46.935626+00:00
-- url     : https://prove2.me/theorems/5471f0cc-df1c-4f74-8885-6b296d61116e
-- title:
--   Proof of Theorem 11, p. 20 — a projected gradient step with α ≤ 1/L_f decreases f by L_f/2 ‖x^{k+1} − x^k‖²
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex and let $f$ be differentiable at every point of $X$ with $L_f$-Lipschitz gradient on $X$, $L_f>0$. Let $0<\alpha_k\le 1/L_f$, $x^k\in X$, and $x^{k+1}=[x^k-\alpha_k\nabla f(x^k)]_X$. Then
--   $$f(x^{k+1})\ \le\ f(x^k)+\Big(\frac{L_f}{2}-\frac1{\alpha_k}\Big)\|x^{k+1}-x^k\|^2\ \le\ f(x^k)-\frac{L_f}{2}\|x^{k+1}-x^k\|^2 .$$
--
--   This is the sufficient-decrease property of (GM): it shows the method is a descent method and is used again in the function-value rates (49) and (50).
--
--   **Formalization Note** Both inequalities of the page's display are stated. Convexity of $f$, closedness of $X$ and the existence of a minimiser are not used and are not hypotheses. The page's step-size window is $\alpha_k\in[\bar L_f^{-1},L_f^{-1}]$; only $0<\alpha_k\le L_f^{-1}$ is used here.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 20, proof of Theorem 11, display after (47)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

open scoped InnerProductSpace

namespace NecoaraNG.GMQuasi

/-- Descent display after (47), proof of Theorem 11, p. 20: for a step size
`0 < α ≤ 1/L_f`, one projected gradient step satisfies
`f(x^{k+1}) ≤ f(x^k) + (L_f/2 - 1/α)‖x^{k+1} - x^k‖² ≤ f(x^k) - L_f/2 ‖x^{k+1} - x^k‖²`. -/
theorem descent_step {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (α : ℝ) (hα : 0 < α) (hαL : α ≤ 1 / Lf) :
    ∀ xk ∈ X, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      f xk1 ≤ f xk + (Lf / 2 - 1 / α) * ‖xk1 - xk‖ ^ 2 ∧
      f xk + (Lf / 2 - 1 / α) * ‖xk1 - xk‖ ^ 2 ≤ f xk - Lf / 2 * ‖xk1 - xk‖ ^ 2 := by sorry

end NecoaraNG.GMQuasi
