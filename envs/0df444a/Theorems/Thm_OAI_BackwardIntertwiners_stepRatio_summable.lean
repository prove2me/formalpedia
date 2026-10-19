-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_stepRatio_summable
-- name    : OAI.BackwardIntertwiners.stepRatio_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:22:19.090705+00:00
-- url     : https://prove2.me/theorems/a972d821-e8a6-4832-b479-8c1f6bf06496
-- title:
--   Summability of the step ratios $w(j+1)/w(j)$ of a weight with quadratically growing convex logarithmic profiles
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Let $w:\mathbb{Z}\to\mathbb{R}$ satisfy $w(j)>0$ for all $j$ and $w(0)=1$, and define $P_w(n)=\log w(-n)$ and $Q_w(n)=-\log w(n)$ for $n\in\mathbb{N}$. Suppose $P_w$ and $Q_w$ are discretely convex and that there is $\delta>0$ with $P_w(n)\ge\delta n^2$ and $Q_w(n)\ge\delta n^2$ for all sufficiently large $n$. Then the step ratios $\rho_w(j)=w(j+1)/w(j)$ are summable over $\mathbb{Z}$:
--   $$\sum_{j\in\mathbb{Z}}\frac{w(j+1)}{w(j)}<\infty.$$
--
--   The hypotheses describe weights that decay at least like $e^{-\delta n^2}$ to the right and grow at least like $e^{\delta n^2}$ to the left, with convex logarithmic profiles; the conclusion says the consecutive ratios of such a weight decay fast in both directions. In the project this summability yields summable tails for coefficient sequences $c$ with $|c_j|\,w_j\le1$.
--
--   **Formalization Note** $P_w$ is `negativeLog w`, $Q_w$ is `positiveLog w` and $\rho_w$ is `stepRatio w`; summability over $\mathbb{Z}$ is Mathlib's unconditional `Summable`, which for these positive terms means convergence of both one-sided series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L211-L235

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.stepRatio_summable {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {δ : ℝ} (hδ : 0 < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    Summable (stepRatio w) := by sorry
