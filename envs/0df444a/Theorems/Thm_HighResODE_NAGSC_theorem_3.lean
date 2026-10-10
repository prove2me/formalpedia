-- Prove2me | Theorems.Thm_HighResODE_NAGSC_theorem_3
-- name    : HighResODE.NAGSC.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:37.474127+00:00
-- url     : https://prove2.me/theorems/405c6395-eb08-45de-a07e-8e9258680bf9
-- title:
--   Theorem 3, p. 16 — NAG-SC with s = 1/(4L): f(xₖ) − f(x⋆) ≤ 5L‖x₀ − x⋆‖²/(1 + √(μ/L)/12)ᵏ
-- statement:
--   **Theorem 3 (Convergence of NAG-SC).** Let $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$, that is, $f$ is differentiable and convex with an $L$-Lipschitz gradient ($L>0$) and is $\mu$-strongly convex with $0<\mu\le L$, and let $x^\star$ be its minimizer. Run Nesterov's accelerated gradient method NAG-SC (1.3) with step size $s=1/(4L)$ from an arbitrary $x_0=y_0$:
--   $$y_{k+1}=x_k-s\nabla f(x_k),\qquad x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k).$$
--   Then, for all $k\ge0$,
--   $$f(x_k)-f(x^\star)\le\frac{5L\|x_0-x^\star\|^2}{\big(1+\frac1{12}\sqrt{\mu/L}\big)^k}.$$
--
--   The bound says $\log(f(x_k)-f(x^\star))\le-\Omega(k\sqrt{\mu/L})$, the optimal accelerated rate for first-order methods on smooth strongly convex functions; the paper obtains it from a single discrete Lyapunov function derived from the high-resolution ODE of NAG-SC.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient f`. The minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z`. The NAG-SC run is the predicate `IsNAGSC f μ (1 / (4 * L)) x y`, which fixes both sequences from $x_0$; iterates are indexed from $0$, and the bound is claimed for every $k$, including $k=0$. The step size is exactly $1/(4L)$, as in the theorem.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 16, Theorem 3

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- Theorem 3 (Convergence of NAG-SC), p. 16: for `f ∈ S¹_{μ,L}(ℝⁿ)` and step size
`s = 1/(4L)`, the NAG-SC iterates satisfy
`f(x_k) − f(x⋆) ≤ 5L‖x₀ − x⋆‖² / (1 + (1/12)√(μ/L))^k` for all `k ≥ 0`. -/
theorem theorem_3 {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, f (x k) - f xs ≤
      5 * L * ‖x 0 - xs‖ ^ 2 / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by sorry

end HighResODE.NAGSC
