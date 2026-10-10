-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_3_15
-- name    : HighResODE.NAGSC.eq_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:21.935986+00:00
-- url     : https://prove2.me/theorems/eae88b44-8d88-427f-8c76-a38e922f891c
-- title:
--   (3.15), proof of Lemma 3.4, p. 19 — upper bound on E(k)
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $0<s\le 1/(4L)$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   Then, for every $k\ge0$,
--   $$\mathcal E(k)\le\Big(\frac{1}{1-\sqrt{\mu s}}+\frac{Ls}{2}\Big)\big(f(x_k)-f(x^\star)\big)+\frac{1+\sqrt{\mu s}+\mu s}{(1-\sqrt{\mu s})^2}\|v_k\|^2+\frac{3\mu}{(1-\sqrt{\mu s})^2}\|x_k-x^\star\|^2+\frac{\sqrt{\mu s}}{1-\sqrt{\mu s}}\Big(f(x_k)-f(x^\star)-\frac s2\|\nabla f(x_k)\|^2\Big).$$
--
--   Compared with the first-difference bound (3.16) at index $k+1$, this gives Lemma 3.4.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page. The page states (3.15) inside the proof of Lemma 3.4, whose standing step-size range $0<s\le1/(4L)$ is taken as the hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 19, (3.15), proof of Lemma 3.4

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (3.15), proof of Lemma 3.4, p. 19: for `f ∈ S¹_{μ,L}(ℝⁿ)` and `0 < s ≤ 1/(4L)`,
the Lyapunov function (2.6) along NAG-SC satisfies
`E(k) ≤ (1/(1 − √(μs)) + Ls/2)(f(x_k) − f(x⋆)) + ((1 + √(μs) + μs)/(1 − √(μs))²)‖v_k‖²
  + (3μ/(1 − √(μs))²)‖x_k − x⋆‖² + (√(μs)/(1 − √(μs)))(f(x_k) − f(x⋆) − (s/2)‖∇f(x_k)‖²)`. -/
theorem eq_3_15 {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hsL : s ≤ 1 / (4 * L)) :
    ∀ k : ℕ, lyap f μ s xs x k ≤
      (1 / (1 - Real.sqrt (μ * s)) + L * s / 2) * (f (x k) - f xs)
        + (1 + Real.sqrt (μ * s) + μ * s) / (1 - Real.sqrt (μ * s)) ^ 2 * ‖vel s x k‖ ^ 2
        + 3 * μ / (1 - Real.sqrt (μ * s)) ^ 2 * ‖x k - xs‖ ^ 2
        + Real.sqrt (μ * s) / (1 - Real.sqrt (μ * s)) *
            (f (x k) - f xs - s / 2 * ‖gradient f (x k)‖ ^ 2) := by sorry

end HighResODE.NAGSC
