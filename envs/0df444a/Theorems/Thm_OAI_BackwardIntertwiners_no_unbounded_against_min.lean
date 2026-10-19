-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_no_unbounded_against_min
-- name    : OAI.BackwardIntertwiners.no_unbounded_against_min
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:21:21.464433+00:00
-- url     : https://prove2.me/theorems/bbe51ead-5337-4213-bea9-05645a8d7d37
-- title:
--   Vanishing positive-lag correlations are impossible against a sequence with a least nonzero index and a summable tail
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Let $B:\mathbb{N}\to\mathbb{R}$ be discretely convex with $B(0)=0$, and suppose there is $\delta>0$ with $B(n)\ge\delta n^2$ for all sufficiently large $n$. Let $b,c:\mathbb{Z}\to\mathbb{C}$ and $h\in\mathbb{Z}$ satisfy:
--   1. $|b(n)|\le e^{-B(n)}$ for every $n\in\mathbb{N}$;
--   2. contact: for every $n\in\mathbb{N}$, if $B(n+2)-2B(n+1)+B(n)>0$ then $|b(n+1)|=e^{-B(n+1)}$;
--   3. $c(h)\neq0$ and $c(j)=0$ for every $j<h$, so $h$ is the least index in the support of $c$;
--   4. for some $p_0\in\mathbb{N}$ the *bounded-side tail* is summable:
--   $$\sum_{k=0}^\infty\tau(p_0,k)<\infty,\qquad\text{where}\quad\tau(p,k)=e^{B(p)-B(p+k+1)}\,|c(h+k+1)|\quad(p,k\in\mathbb{N}).$$
--
--   Then it is impossible that
--   $$\sum_{j\in\mathbb{Z}}b(j)\,c(j-r)=0\qquad\text{for every integer }r\ge1.$$
--
--   Note that hypotheses 1–2 and the quadratic growth of $B$ force $b(p)\neq0$ whenever $B$ has a strict corner at $p$, i.e. $\Delta^2B(p-1)>0$, and there are infinitely many such $p$, so $b$ has unbounded support to the right. The theorem is the one-sided counterpart of the obstruction for supports unbounded in both directions: it handles the case where $c$ has a least nonzero index, and is used to show that the support of $b$ must then be bounded above.
--
--   **Formalization Note** $\tau(p,k)$ is `boundedSideTail B c h p k`, and the conclusion is `False`. The summability in hypothesis 4 is genuine (`Summable`), while the correlations are Mathlib's unconditional sums `tsum`, which are $0$ for non-summable families; so the hypothesis that they vanish is no stronger than requiring the series to converge to $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L137-L204

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.no_unbounded_against_min {B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hB : DiscreteConvex B) (hB0 : B 0 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hquad : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ B n)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ Real.exp (-B n))
    (hc : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1:ℕ):ℤ)‖ = Real.exp (-B (n+1)))
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    {p₀ : ℕ} (hsum : Summable (boundedSideTail B c h p₀))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by sorry
