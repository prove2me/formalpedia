-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_3_8
-- name    : HighResODE.NAGSC.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:20.173515+00:00
-- url     : https://prove2.me/theorems/a5e8515d-e1ac-4520-a108-be5b63180f93
-- title:
--   (3.8), proof of Theorem 3, p. 17 — E(k) ≤ E(0)/(1 + √(μs)/6)ᵏ = E(0)/(1 + √(μ/L)/12)ᵏ at s = 1/(4L)
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $s=1/(4L)$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   Then, for every $k\ge0$,
--   $$\mathcal E(k)\le\frac{\mathcal E(0)}{\big(1+\frac{\sqrt{\mu s}}{6}\big)^k}=\frac{\mathcal E(0)}{\big(1+\frac1{12}\sqrt{\mu/L}\big)^k}.$$
--
--   This is Lemma 3.4 applied inductively, written at the step size of Theorem 3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page. Both the inequality and the equality of the display are stated, with $s$ replaced by `1 / (4 * L)`.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 17, (3.8), proof of Theorem 3

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (3.8), proof of Theorem 3, p. 17: for `f ∈ S¹_{μ,L}(ℝⁿ)` and `s = 1/(4L)`, along NAG-SC,
`E(k) ≤ E(0)/(1 + √(μs)/6)^k = E(0)/(1 + (1/12)√(μ/L))^k`. -/
theorem eq_3_8 {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, lyap f μ (1 / (4 * L)) xs x k ≤
        lyap f μ (1 / (4 * L)) xs x 0 / (1 + Real.sqrt (μ * (1 / (4 * L))) / 6) ^ k ∧
      lyap f μ (1 / (4 * L)) xs x 0 / (1 + Real.sqrt (μ * (1 / (4 * L))) / 6) ^ k =
        lyap f μ (1 / (4 * L)) xs x 0 / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by sorry

end HighResODE.NAGSC
