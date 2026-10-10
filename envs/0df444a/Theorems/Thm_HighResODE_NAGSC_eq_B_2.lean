-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_B_2
-- name    : HighResODE.NAGSC.eq_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:30.898988+00:00
-- url     : https://prove2.me/theorems/3a3ed397-dacd-45fa-b637-9f4ef7681574
-- title:
--   (B.2), App. B.2.1, p. 51 — first-difference bound for E(k) along NAG-SC
-- statement:
--   Throughout, $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$: $f$ is differentiable and convex on $\mathbb R^n$, its gradient is $L$-Lipschitz with $L>0$, and $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2$ for all $x,y$, with $0<\mu\le L$. The point $x^\star$ is a minimizer of $f$, and $(x_k,y_k)_{k\ge0}$ are the iterates of NAG-SC with step size $s$: $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$.
--
--   Let $0<s\le 1/(4L)$. $v_k=(x_{k+1}-x_k)/\sqrt s$ is the velocity and $\mathcal E(k)$ is the discrete Lyapunov function (2.6),
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   Then, for every $k\ge0$,
--   $$\mathcal E(k+1)-\mathcal E(k)\le-\frac{\sqrt{\mu s}}{1-\sqrt{\mu s}}\Big[\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\Big(\langle\nabla f(x_{k+1}),x_{k+1}-x^\star\rangle-s\|\nabla f(x_{k+1})\|^2\Big)+\|v_{k+1}\|^2\Big]-\frac12\Big(\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}\Big)\Big(\frac1L-s\Big)\|\nabla f(x_{k+1})-\nabla f(x_k)\|^2.$$
--
--   Combined with the two lower bounds on $f(x^\star)$ for $f\in\mathcal S^1_{\mu,L}$, this yields (3.16).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient f`, and the minimizer $x^\star$ is a point `xs` with `∀ z, f xs ≤ f z` (for strongly convex $f$ one exists; the paper presupposes it). Iterates are indexed from $k=0$, as on the page. The page prints (B.2) without a step-size range; it is derived (App. B.2.2) and used only within the proof of Lemma 3.4, so that lemma's range $0<s\le1/(4L)$ is taken as the hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 51, (B.2), Appendix B.2.1

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (B.2), App. B.2.1, p. 51: for `f ∈ S¹_{μ,L}(ℝⁿ)` and `0 < s ≤ 1/(4L)`, along NAG-SC,
`E(k+1) − E(k) ≤ −(√(μs)/(1 − √(μs)))[((1 + √(μs))/(1 − √(μs)))(⟨∇f(x_{k+1}), x_{k+1} − x⋆⟩
  − s‖∇f(x_{k+1})‖²) + ‖v_{k+1}‖²]
  − ½((1 + √(μs))/(1 − √(μs)) + (1 − √(μs))/(1 + √(μs)))(1/L − s)‖∇f(x_{k+1}) − ∇f(x_k)‖²`. -/
theorem eq_B_2 {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hsL : s ≤ 1 / (4 * L)) :
    ∀ k : ℕ, lyap f μ s xs x (k + 1) - lyap f μ s xs x k ≤
      -(Real.sqrt (μ * s) / (1 - Real.sqrt (μ * s))) *
          ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) *
              (⟪gradient f (x (k + 1)), x (k + 1) - xs⟫_ℝ
                - s * ‖gradient f (x (k + 1))‖ ^ 2)
            + ‖vel s x (k + 1)‖ ^ 2)
        - 1 / 2 * ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))
            + (1 - Real.sqrt (μ * s)) / (1 + Real.sqrt (μ * s))) * (1 / L - s) *
          ‖gradient f (x (k + 1)) - gradient f (x k)‖ ^ 2 := by sorry

end HighResODE.NAGSC
