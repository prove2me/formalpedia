-- Prove2me | Theorems.Thm_HessianDamping_DINSC_strong_convexity_ineq
-- name    : HessianDamping.DINSC.strong_convexity_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:50.239625+00:00
-- url     : https://prove2.me/theorems/190d8965-de0f-4026-9011-d90019818c7e
-- title:
--   Proof of Theorem 7, p. 20 — ⟨∇f(y), y − x⋆⟩ ≥ f(y) − f(x⋆) + (μ/2)‖y − x⋆‖² for μ-strongly convex f
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f:\mathcal H\to\mathbb R$ a convex function of class $\mathcal C^2$ which is $\mu$-strongly convex for some $\mu>0$, that is, $f-\frac{\mu}{2}\|\cdot\|^2$ is convex. Let $x^\star$ be a minimizer of $f$. Then for every $y\in\mathcal H$,
--   $$\langle\nabla f(y),\,y-x^\star\rangle\ \ge\ f(y)-f(x^\star)+\frac{\mu}{2}\|y-x^\star\|^2 .$$
--
--   In the proof of Theorem 7 this is applied at $y=x(t)$; it is the only place where strong convexity enters the differential inequality for the Lyapunov function.
--
--   **Formalization Note.** The page states the inequality at $y=x(t)$ on a trajectory; it is stated here at every point $y$, which is the same claim since $x(t)$ is arbitrary. The minimizer is a point $x^\star$ with $f(x^\star)\le f(y)$ for all $y$, the concrete form of the standing hypothesis $\operatorname{argmin} f\neq\emptyset$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 20, §4.1, proof of Theorem 7 (i), display after 'By strong convexity of f we have'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7, p. 20: the strong convexity inequality
`⟨∇f(y), y − x⋆⟩ ≥ f(y) − f(x⋆) + (μ/2)‖y − x⋆‖²`, at every point `y`. -/
theorem strong_convexity_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y) :
    ∀ y : H, f y - f xstar + μ / 2 * ‖y - xstar‖ ^ 2 ≤ inner ℝ (gradient f y) (y - xstar) := by sorry

end HessianDamping.DINSC
