-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_theorem_5
-- name    : HighResODE.NAGCODE.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:59.651992+00:00
-- url     : https://prove2.me/theorems/486b6c24-a910-404c-8edc-7296e9370f08
-- title:
--   Theorem 5, p. 21 — along the high-resolution ODE of NAG-C, inf_{t₀≤u≤t}‖∇f(X(u))‖² ≤ (12 + 9sL)‖x₀ − x⋆‖²/(2√s(t³ − t₀³))
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$ be an $L$-smooth convex function with Lipschitz-continuous Hessian, and let $x^\star$ be a minimizer of $f$. Fix an arbitrary step size $s>0$, put $t_0=1.5\sqrt s$, and let $X=X(t)$ solve the high-resolution ODE of NAG-C
--   $$\ddot X(t)+\frac3t\dot X(t)+\sqrt s\,\nabla^2 f(X(t))\dot X(t)+\Big(1+\frac{3\sqrt s}{2t}\Big)\nabla f(X(t))=0\quad(t\ge t_0),\qquad X(t_0)=x_0,\ \dot X(t_0)=-\sqrt s\,\nabla f(x_0).$$
--   Then the squared gradient norm satisfies
--   $$\inf_{t_0\le u\le t}\|\nabla f(X(u))\|^2\le\frac{(12+9sL)\|x_0-x^\star\|^2}{2\sqrt s\,(t^3-t_0^3)}\qquad\text{for all }t>t_0 .$$
--
--   With $s=1/L$ this is an $O(\sqrt L/t^3)$ rate for the squared gradient norm, faster than the $O(L/t^2)$ that follows from the function-value rate. It is the continuous-time counterpart of the inverse cubic rate of NAG-C (Theorem 6 of the paper), and it is driven by the Hessian (gradient-correction) term, which the low-resolution ODE lacks.
--
--   **Formalization Note** The statement holds for every solution $(X,\dot X)$ of the ODE on $[t_0,\infty)$; existence and uniqueness of the solution (Proposition 2.2 of the paper) are not assumed. The minimizer $x^\star$ is assumed to exist, as the paper presupposes. The infimum is over the points of $[t_0,t]$. The step size is unrestricted: there is no condition $s\le1/L$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 21, Theorem 5

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- Theorem 5, p. 21: for `f ∈ F²_L(ℝⁿ)`, any step size `s > 0` and the solution `X` of (1.12),
`inf_{t₀≤u≤t} ‖∇f(X(u))‖² ≤ (12 + 9sL)‖x₀ − x⋆‖²/(2√s(t³ − t₀³))` for all `t > t₀ = 1.5√s`. -/
theorem theorem_5 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s < t →
      (⨅ u : Set.Icc (t0 s) t, ‖gradient f (X u)‖ ^ 2)
        ≤ (12 + 9 * s * L) * ‖x0 - xs‖ ^ 2 / (2 * Real.sqrt s * (t ^ 3 - (t0 s) ^ 3)) := by sorry

end HighResODE.NAGCODE
