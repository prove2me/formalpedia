-- Prove2me | Theorems.Thm_NecoaraNG_GMQuasi_optimality_47
-- name    : NecoaraNG.GMQuasi.optimality_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:45.801974+00:00
-- url     : https://prove2.me/theorems/1b4a059c-c6ee-4547-b227-a7c4e968e780
-- title:
--   (47), p. 20 — optimality conditions of the projected gradient step
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex, let $f$ be a function with gradient $\nabla f$, let $x^k\in X$ and $\alpha_k\in\mathbb R$, and let $x^{k+1}=[x^k-\alpha_k\nabla f(x^k)]_X$ be a nearest point of $X$ to $x^k-\alpha_k\nabla f(x^k)$. Then
--   $$\langle x^{k+1}-x^k+\alpha_k\nabla f(x^k),\,x-x^{k+1}\rangle\ \ge\ 0\qquad\forall x\in X. \tag{47}$$
--
--   This is the variational characterisation of the Euclidean projection, specialised to one step of the projected gradient method (GM); every later inequality of the proof of Theorem 11 starts from it.
--
--   **Formalization Note** Only convexity of $X$ is used, so closedness of $X$, convexity and smoothness of $f$ and the sign of $\alpha_k$ are not hypotheses (the statement is stronger than needed and still true). $x^{k+1}$ is any nearest point.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 20, proof of Theorem 11, (47)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

open scoped InnerProductSpace

namespace NecoaraNG.GMQuasi

/-- (47), proof of Theorem 11, p. 20: the optimality conditions of the projection step
`x^{k+1} = [x^k - α_k ∇f(x^k)]_X`. -/
theorem optimality_47 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X) (f : NecoaraNG.Chain.E n → ℝ) :
    ∀ xk ∈ X, ∀ α : ℝ, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      ∀ x ∈ X, 0 ≤ ⟪xk1 - xk + α • gradient f xk, x - xk1⟫_ℝ := by sorry

end NecoaraNG.GMQuasi
