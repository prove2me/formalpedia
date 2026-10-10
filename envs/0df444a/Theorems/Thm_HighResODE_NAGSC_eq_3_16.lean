-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_3_16
-- name    : HighResODE.NAGSC.eq_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:34.374615+00:00
-- url     : https://prove2.me/theorems/3696edf9-5f5a-4f1a-800f-87ac5b54d7fa
-- title:
--   (3.16), pp. 19–20 — first-difference bound for E(k) when s ≤ 1/(2L)
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $0<s\le 1/(2L)$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   Then, for every $k\ge0$,
--   $$\mathcal E(k+1)-\mathcal E(k)\le-\sqrt{\mu s}\Big[\frac{1-2Ls}{(1-\sqrt{\mu s})^2}\big(f(x_{k+1})-f(x^\star)\big)+\frac{1}{1-\sqrt{\mu s}}\|v_{k+1}\|^2+\frac{\mu}{2(1-\sqrt{\mu s})^2}\|x_{k+1}-x^\star\|^2+\frac{\sqrt{\mu s}}{(1-\sqrt{\mu s})^2}\Big(f(x_{k+1})-f(x^\star)-\frac s2\|\nabla f(x_{k+1})\|^2\Big)\Big].$$
--
--   Comparing coefficients with (3.15) at index $k+1$ gives Lemma 3.4.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page. The range $s\le1/(2L)$ is the page's ("holds for $s\le1/(2L)$"); $s>0$ is added because $\sqrt s$ and $1/\sqrt s$ appear in $v_k$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, pp. 19–20, (3.16)

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (3.16), pp. 19–20: for `f ∈ S¹_{μ,L}(ℝⁿ)` and `0 < s ≤ 1/(2L)`, along NAG-SC,
`E(k+1) − E(k) ≤ −√(μs)[((1 − 2Ls)/(1 − √(μs))²)(f(x_{k+1}) − f(x⋆))
  + (1/(1 − √(μs)))‖v_{k+1}‖² + (μ/(2(1 − √(μs))²))‖x_{k+1} − x⋆‖²
  + (√(μs)/(1 − √(μs))²)(f(x_{k+1}) − f(x⋆) − (s/2)‖∇f(x_{k+1})‖²)]`. -/
theorem eq_3_16 {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hsL : s ≤ 1 / (2 * L)) :
    ∀ k : ℕ, lyap f μ s xs x (k + 1) - lyap f μ s xs x k ≤
      -Real.sqrt (μ * s) *
        ((1 - 2 * L * s) / (1 - Real.sqrt (μ * s)) ^ 2 * (f (x (k + 1)) - f xs)
          + 1 / (1 - Real.sqrt (μ * s)) * ‖vel s x (k + 1)‖ ^ 2
          + μ / (2 * (1 - Real.sqrt (μ * s)) ^ 2) * ‖x (k + 1) - xs‖ ^ 2
          + Real.sqrt (μ * s) / (1 - Real.sqrt (μ * s)) ^ 2 *
              (f (x (k + 1)) - f xs - s / 2 * ‖gradient f (x (k + 1))‖ ^ 2)) := by sorry

end HighResODE.NAGSC
