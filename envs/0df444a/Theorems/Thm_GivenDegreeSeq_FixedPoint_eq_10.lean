-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_eq_10
-- name    : GivenDegreeSeq.FixedPoint.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:25.183271+00:00
-- url     : https://prove2.me/theorems/ff20e3ff-0081-4067-b5fc-344bdfa61a9c
-- title:
--   (10) — a uniform $\theta(|\hat\beta|_\infty,|x_0|_\infty)<1$ with $|x_{k+3}-x_{k+2}|_\infty\le\theta|x_{k+1}-x_k|_\infty$ and $|x_{k+2}-\hat\beta|_\infty\le\theta|x_k-\hat\beta|_\infty$
-- statement:
--   There is a function $\Theta:\mathbb R^2\to[0,1)$, continuous, with the following property. Let $n\ge3$, let $d_1,\dots,d_n>0$, let $\varphi$ be the map of (5), and suppose $\varphi$ has a fixed point $\hat\beta$. For any $x_0\in\mathbb R^n$ define $x_{k+1}=\varphi(x_k)$ for $k\ge0$, and put $\theta=\Theta(|\hat\beta|_\infty,|x_0|_\infty)$. Then for every $k\ge0$,
--   $$|x_{k+1}-\hat\beta|_\infty\le|x_k-\hat\beta|_\infty,$$
--   $$|x_{k+3}-x_{k+2}|_\infty\le\theta\,|x_{k+1}-x_k|_\infty,\tag{10}$$
--   $$|x_{k+2}-\hat\beta|_\infty\le\theta\,|x_k-\hat\beta|_\infty.$$
--
--   The contraction factor depends only on $|\hat\beta|_\infty$ and $|x_0|_\infty$, and not on the number of vertices $n$ or on the degrees; this uniformity is what makes the iteration a practical algorithm in high dimension.
--
--   **Formalization Note** "A single $\theta\in[0,1)$ depending only on $|\hat\beta|_\infty$ and $|x_0|_\infty$ in a continuous manner" is rendered by choosing the function $\Theta$ first, before $n$, $d$, $\hat\beta$, $x_0$ and $k$. The hypothesis $n\ge3$ is needed: for $n=2$ the two-step factor of (9) equals $1$. The iterates are $x_k=\varphi^{k}(x_0)$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 13, Eq. (10) and the two displays around it

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

/-- (10), p. 13: there is `Θ(a, b) ∈ [0, 1)`, continuous in `(a, b)` and independent of `n`
and `d`, such that whenever `n ≥ 3`, `d > 0`, `β̂` is a fixed point of `φ` and
`x_k = φ^k(x₀)`, for every `k ≥ 0`:
`|x_{k+1} − β̂|∞ ≤ |x_k − β̂|∞`,
`|x_{k+3} − x_{k+2}|∞ ≤ Θ(|β̂|∞, |x₀|∞) |x_{k+1} − x_k|∞` and
`|x_{k+2} − β̂|∞ ≤ Θ(|β̂|∞, |x₀|∞) |x_k − β̂|∞`. -/
theorem eq_10 :
    ∃ Θ : ℝ → ℝ → ℝ, Continuous (Function.uncurry Θ) ∧ (∀ a b, 0 ≤ Θ a b ∧ Θ a b < 1) ∧
      ∀ n : ℕ, 3 ≤ n → ∀ d : Fin n → ℝ, (∀ i, 0 < d i) →
        ∀ βhat : Fin n → ℝ, phi d βhat = βhat → ∀ (x₀ : Fin n → ℝ) (k : ℕ),
          ‖(phi d)^[k + 1] x₀ - βhat‖ ≤ ‖(phi d)^[k] x₀ - βhat‖ ∧
          ‖(phi d)^[k + 3] x₀ - (phi d)^[k + 2] x₀‖ ≤
            Θ ‖βhat‖ ‖x₀‖ * ‖(phi d)^[k + 1] x₀ - (phi d)^[k] x₀‖ ∧
          ‖(phi d)^[k + 2] x₀ - βhat‖ ≤ Θ ‖βhat‖ ‖x₀‖ * ‖(phi d)^[k] x₀ - βhat‖ := by sorry

end GivenDegreeSeq.FixedPoint
