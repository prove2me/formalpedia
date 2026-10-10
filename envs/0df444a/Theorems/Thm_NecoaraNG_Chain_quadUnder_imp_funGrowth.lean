-- Prove2me | Theorems.Thm_NecoaraNG_Chain_quadUnder_imp_funGrowth
-- name    : NecoaraNG.Chain.quadUnder_imp_funGrowth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:13.927503+00:00
-- url     : https://prove2.me/theorems/c6ed9470-ad40-4c55-b397-98e4572d0813
-- title:
--   Proof of Theorem 4, p. 9 — quadratic under-approximation (13) implies quadratic functional growth (22) with the same κ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f$ be convex on $X$, differentiable at every point of $X$, with $L_f$-Lipschitz gradient on $X$ ($L_f>0$), and assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty. Let $\kappa>0$ and let $\bar x=[x]_{X^*}$. If
--   $$f(x)\ge f^*+\langle\nabla f(\bar x),x-\bar x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X,$$
--   then
--   $$f(x)-f^*\ge\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X.$$
--
--   In class notation: $\mathcal U_{L_f,\kappa}(X)\subseteq\mathcal F_{L_f,\kappa}(X)$, the last link of (23).
--
--   **Formalization Note** $f^*$ is written $f(\bar x)$. The paper's standing assumptions are kept as hypotheses; the implication only needs the first-order optimality condition at $\bar x$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 9, proof of Theorem 4, first two sentences

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Proof of Theorem 4, p. 9: inequality (13) implies inequality (22), with the same constant `κ`. -/
theorem quadUnder_imp_funGrowth {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    QuadUnder X f κ → QuadFunGrowth X f κ := by sorry

end NecoaraNG.Chain
