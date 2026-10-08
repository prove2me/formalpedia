-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_eq_6_7
-- name    : GivenDegreeSeq.FixedPoint.eq_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:29.572254+00:00
-- url     : https://prove2.me/theorems/605e8509-04b5-4eac-b9bc-ff7d2739bff5
-- title:
--   (6)–(7) — bounds $-e^{2K}/(n-1)\le\partial\varphi_i/\partial x_j\le-e^{-4K}/(2(n-1))$ and $\tfrac12e^{-4K}\le\partial\varphi_i/\partial x_i\le e^{2K}$ on $|x|_\infty\le K$
-- statement:
--   Let $n\ge2$, $d_1,\dots,d_n>0$, and let $\varphi$ be the map of (5). Let $K\in\mathbb R$ and $x\in\mathbb R^n$ with $|x|_\infty=\max_i|x_i|\le K$. Then for every $1\le i\ne j\le n$,
--   $$-\frac{e^{2K}}{n-1}\le\frac{\partial\varphi_i}{\partial x_j}(x)\le-\frac{e^{-4K}}{2(n-1)},\tag{6}$$
--   and for every $1\le i\le n$,
--   $$\frac12e^{-4K}\le\frac{\partial\varphi_i}{\partial x_i}(x)\le e^{2K}.\tag{7}$$
--
--   These bounds show that on a sup-norm ball the Jacobian of $\varphi$ has diagonal entries bounded below and off-diagonal entries bounded away from $0$ from below, uniformly in $n$ after scaling by $n-1$; they are what places the averaged Jacobian $J(x,y)$ in a class $\mathcal L_n(\delta)$.
--
--   **Formalization Note** The partial derivative is the Fréchet derivative of $\varphi_i$ applied to the $j$-th unit vector. The hypothesis $|x|_\infty\le K$ forces $K\ge0$. The derivatives do not depend on $d$; $d_i>0$ is the standing assumption under which $\varphi$ is defined.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 12, Eqs. (6)–(7)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

/-- (6)–(7), p. 12: if `|x|∞ ≤ K` then for `i ≠ j`
`−e^{2K}/(n − 1) ≤ ∂φ_i/∂x_j(x) ≤ −e^{−4K}/(2(n − 1))`, and for every `i`
`½ e^{−4K} ≤ ∂φ_i/∂x_i(x) ≤ e^{2K}`. -/
theorem eq_6_7 {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (K : ℝ) (x : Fin n → ℝ) (hx : ‖x‖ ≤ K) :
    (∀ i j : Fin n, i ≠ j →
        -Real.exp (2 * K) / ((n : ℝ) - 1) ≤ partialPhi d x i j ∧
        partialPhi d x i j ≤ -Real.exp (-4 * K) / (2 * ((n : ℝ) - 1))) ∧
    (∀ i : Fin n,
        Real.exp (-4 * K) / 2 ≤ partialPhi d x i i ∧
        partialPhi d x i i ≤ Real.exp (2 * K)) := by sorry

end GivenDegreeSeq.FixedPoint
