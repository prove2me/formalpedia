-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_bounded_above_of_min
-- name    : OAI.BackwardIntertwiners.bounded_above_of_min
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:23:21.85198+00:00
-- url     : https://prove2.me/theorems/babecb5b-7e6c-481a-a887-aadafe426dfc
-- title:
--   If $c$ has a least nonzero index, vanishing positive-lag correlations force the support of $b$ to be bounded above
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Let $w:\mathbb{Z}\to\mathbb{R}$ be a weight with $w(j)>0$ for all $j$, nonincreasing ($w(i)\ge w(j)$ for $i\le j$), and $w(0)=1$. Suppose that the step ratios are summable, $\sum_{j\in\mathbb{Z}}w(j+1)/w(j)<\infty$, that $Q_w(n)=-\log w(n)$ is discretely convex on $\mathbb{N}$, and that $Q_w(n)\ge\delta n^2$ for all sufficiently large $n$, for some $\delta>0$. Let $b,c:\mathbb{Z}\to\mathbb{C}$ satisfy
--   $$|b_j|\le w(j),\qquad|c_j|\,w(j)\le1\qquad(j\in\mathbb{Z}),$$
--   let $h\in\mathbb{Z}$ with $c_h\neq0$ and $c_j=0$ for all $j<h$, and assume
--   $$\sum_{j\in\mathbb{Z}}b_j\,c_{j-r}=0\qquad\text{for every integer }r\ge1.$$
--   Then the support of $b$ is bounded above: there is $m\in\mathbb{Z}$ such that $b_j\neq0$ implies $j\le m$.
--
--   This is one half of the support separation property for such weights: if $b$ and $c$ are nonzero, $|b|\le w$, $|c|\,w\le1$ and all positive-lag correlations vanish, then $b$ should have a largest nonzero index $t$ and $c$ a least nonzero index $h$ with $t\le h$. The theorem shows that a least nonzero index of $c$ forces the existence of an upper bound for the support of $b$.
--
--   **Formalization Note** Monotonicity is `Antitone w`, the step ratio is `stepRatio w` with `Summable` over $\mathbb{Z}$, and $Q_w$ is `positiveLog w`. The correlations are Mathlib's unconditional sums `tsum`, which are $0$ for non-summable families, so the hypothesis that they vanish is no stronger than requiring the series to converge to $0$. No convexity or growth assumption is made on the left profile $\log w(-n)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L288-L308

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.bounded_above_of_min {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1) (hs : Summable (stepRatio w))
    (hQ : DiscreteConvex (positiveLog w)) {δ : ℝ} (hδ : 0 < δ)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n)
    {b c : ℤ → ℂ} (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖*w j ≤ 1)
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ m : ℤ, ∀ j : ℤ, b j ≠ 0 → j ≤ m := by sorry
