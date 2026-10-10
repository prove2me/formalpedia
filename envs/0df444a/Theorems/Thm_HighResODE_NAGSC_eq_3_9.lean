-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_3_9
-- name    : HighResODE.NAGSC.eq_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:34.632344+00:00
-- url     : https://prove2.me/theorems/aed3e4f2-5635-42ea-b52d-d6436f744db5
-- title:
--   (3.9), proof of Theorem 3, p. 17 — bound on E(0) in terms of L‖x₀ − x⋆‖²
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $s>0$ with $\mu s<1$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   The initial velocity is $v_0=-2\sqrt s\,\nabla f(x_0)/(1+\sqrt{\mu s})$. Then
--   $$\begin{aligned}\mathcal E(0)&\le\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_0)-f(x^\star)\big)+\frac{s}{(1+\sqrt{\mu s})^2}\|\nabla f(x_0)\|^2+\frac14\Big\|\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_0-x^\star)-\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\sqrt s\,\nabla f(x_0)\Big\|^2\\&\le\Big[\frac12\Big(\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\Big)+\frac{Ls}{(1+\sqrt{\mu s})^2}+\frac{2\mu/L}{(1-\sqrt{\mu s})^2}+\frac{Ls}{2}\Big(\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\Big)^2\Big]\cdot L\|x_0-x^\star\|^2.\end{aligned}$$
--
--   With $s=1/(4L)$ this bounds the initial value of the Lyapunov function, which, with (3.7) and (3.8), gives Theorem 3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page. The page states (3.9) for a general step size before specializing to $s=1/(4L)$; the hypotheses $s>0$ and $\mu s<1$ are exactly what makes $v_0$ and every quotient $1/(1-\sqrt{\mu s})$ meaningful. Both inequalities of the display are stated.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 17, (3.9), proof of Theorem 3

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (3.9), proof of Theorem 3, p. 17: for `f ∈ S¹_{μ,L}(ℝⁿ)` and a step size `s > 0` with
`μs < 1`, along NAG-SC (initial velocity `v₀ = −2√s∇f(x₀)/(1 + √(μs))`),
`E(0) ≤ ((1 + √(μs))/(1 − √(μs)))(f(x₀) − f(x⋆)) + (s/(1 + √(μs))²)‖∇f(x₀)‖²
  + ¼‖(2√μ/(1 − √(μs)))(x₀ − x⋆) − ((1 + √(μs))/(1 − √(μs)))√s∇f(x₀)‖²
  ≤ [½((1 + √(μs))/(1 − √(μs))) + Ls/(1 + √(μs))² + (2μ/L)/(1 − √(μs))²
     + (Ls/2)((1 + √(μs))/(1 − √(μs)))²] · L‖x₀ − x⋆‖²`. -/
theorem eq_3_9 {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hμs : μ * s < 1) :
    lyap f μ s xs x 0 ≤
        (1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) * (f (x 0) - f xs)
          + s / (1 + Real.sqrt (μ * s)) ^ 2 * ‖gradient f (x 0)‖ ^ 2
          + 1 / 4 * ‖(2 * Real.sqrt μ / (1 - Real.sqrt (μ * s))) • (x 0 - xs)
              - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
                  (Real.sqrt s • gradient f (x 0))‖ ^ 2 ∧
      (1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) * (f (x 0) - f xs)
          + s / (1 + Real.sqrt (μ * s)) ^ 2 * ‖gradient f (x 0)‖ ^ 2
          + 1 / 4 * ‖(2 * Real.sqrt μ / (1 - Real.sqrt (μ * s))) • (x 0 - xs)
              - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
                  (Real.sqrt s • gradient f (x 0))‖ ^ 2 ≤
        (1 / 2 * ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)))
            + L * s / (1 + Real.sqrt (μ * s)) ^ 2
            + 2 * μ / L / (1 - Real.sqrt (μ * s)) ^ 2
            + L * s / 2 * ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) ^ 2) *
          L * ‖x 0 - xs‖ ^ 2 := by sorry

end HighResODE.NAGSC
