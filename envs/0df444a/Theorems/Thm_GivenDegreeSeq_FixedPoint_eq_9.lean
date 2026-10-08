-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_eq_9
-- name    : GivenDegreeSeq.FixedPoint.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:36.185598+00:00
-- url     : https://prove2.me/theorems/b1384d77-291a-4c9a-93ef-5f0e6477a6b1
-- title:
--   (9) — $|\varphi(\varphi(x))-\varphi(\varphi(y))|_\infty\le\theta(x,y)|x-y|_\infty$, and $|\varphi(x)-\varphi(y)|_\infty\le|x-y|_\infty$
-- statement:
--   Let $n\ge2$, $d_1,\dots,d_n>0$, and let $\varphi$ be the map of (5). For $x,y\in\mathbb R^n$ let $K$ be the maximum of the sup norms $|x|_\infty$, $|y|_\infty$, $|\varphi(x)|_\infty$, $|\varphi(y)|_\infty$, let $\delta=\tfrac12e^{-4K}$, and let
--   $$\theta(x,y)=1-\frac{2(n-2)\delta^2}{n-1}.$$
--   Then
--
--   1. $$|\varphi(\varphi(x))-\varphi(\varphi(y))|_\infty\le\theta(x,y)\,|x-y|_\infty;\tag{9}$$
--   2. $0\le\theta(x,y)$, and $\theta(x,y)<1$ when $n\ge3$;
--   3. $|\varphi(x)-\varphi(y)|_\infty\le|x-y|_\infty$.
--
--   The two-step map $\varphi\circ\varphi$ is therefore a strict contraction on every bounded set, with a contraction factor depending only on a bound for the norms involved, while $\varphi$ itself is non-expansive.
--
--   **Formalization Note** The paper states $0\le\theta<1$ without a condition on $n$; for $n=2$ one has $\theta=1$, so the strict inequality is stated for $n\ge3$, while (9) and the non-expansiveness hold for all $n\ge2$. The paper's further remark that $\theta$ is uniformly bounded away from $1$ on (bounded) subsets is not stated here; its quantitative form is (10).
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 12–13, Eq. (9) and the bound |φ(x) − φ(y)|∞ ≤ |x − y|∞

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

/-- (9), p. 13: with `K` the maximum of `|x|∞, |y|∞, |φ(x)|∞, |φ(y)|∞` and `δ = ½ e^{−4K}`,
`θ(x, y) = 1 − 2(n − 2)δ²/(n − 1)` satisfies
`|φ(φ(x)) − φ(φ(y))|∞ ≤ θ(x, y) |x − y|∞`; `0 ≤ θ(x, y)`, and `θ(x, y) < 1` when `n ≥ 3`;
and `|φ(x) − φ(y)|∞ ≤ |x − y|∞`. -/
theorem eq_9 {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (x y : Fin n → ℝ) :
    let K : ℝ := max (max ‖x‖ ‖y‖) (max ‖phi d x‖ ‖phi d y‖)
    let δ : ℝ := Real.exp (-4 * K) / 2
    let θ : ℝ := 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1)
    ‖phi d (phi d x) - phi d (phi d y)‖ ≤ θ * ‖x - y‖ ∧
    0 ≤ θ ∧ (3 ≤ n → θ < 1) ∧
    ‖phi d x - phi d y‖ ≤ ‖x - y‖ := by sorry

end GivenDegreeSeq.FixedPoint
