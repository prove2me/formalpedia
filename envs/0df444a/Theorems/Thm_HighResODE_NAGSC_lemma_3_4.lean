-- Prove2me | Theorems.Thm_HighResODE_NAGSC_lemma_3_4
-- name    : HighResODE.NAGSC.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:36.559286+00:00
-- url     : https://prove2.me/theorems/8db982d4-fa1b-4265-9b25-fb7584e0fdc4
-- title:
--   Lemma 3.4, p. 16 — E(k + 1) − E(k) ≤ −(√(μs)/6) E(k + 1) along NAG-SC for 0 < s ≤ 1/(4L)
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $0<s\le 1/(4L)$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   Then, for every $k\ge0$,
--   $$\mathcal E(k+1)-\mathcal E(k)\le-\frac{\sqrt{\mu s}}{6}\,\mathcal E(k+1).$$
--
--   Equivalently $\mathcal E(k+1)\le\mathcal E(k)/(1+\sqrt{\mu s}/6)$: the Lyapunov function decays geometrically at a rate governed by $\sqrt{\mu s}$, the discrete analogue of Lemma 3.1 for the high-resolution ODE. It is the engine of Theorem 3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 16, Lemma 3.4

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- Lemma 3.4 (Lyapunov function for NAG-SC), p. 16: for `f ∈ S¹_{μ,L}(ℝⁿ)` and any step
size `0 < s ≤ 1/(4L)`, the discrete Lyapunov function (2.6) along NAG-SC satisfies
`E(k + 1) − E(k) ≤ −(√(μs)/6) E(k + 1)`. -/
theorem lemma_3_4 {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hsL : s ≤ 1 / (4 * L)) :
    ∀ k : ℕ, lyap f μ s xs x (k + 1) - lyap f μ s xs x k ≤
      -(Real.sqrt (μ * s) / 6) * lyap f μ s xs x (k + 1) := by sorry

end HighResODE.NAGSC
