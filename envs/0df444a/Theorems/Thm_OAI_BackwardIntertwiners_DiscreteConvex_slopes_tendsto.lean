-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_slopes_tendsto
-- name    : OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:17:08.359501+00:00
-- url     : https://prove2.me/theorems/4ae59311-337a-447c-b2fe-f375070b573b
-- title:
--   Quadratic growth forces the increments of a discretely convex sequence to diverge
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$.
--
--   Let $F:\mathbb{N}\to\mathbb{R}$ be discretely convex with $F(0)=0$, and suppose there is $\delta>0$ such that $F(n)\ge\delta n^2$ for all sufficiently large $n$. Then
--   $$\lim_{n\to\infty}\bigl(F(n+1)-F(n)\bigr)=+\infty.$$
--
--   For a convex profile, quadratic growth of the values thus forces unbounded growth of the slopes. In the project the logarithmic profiles of the weights are of this kind, and divergence of their increments is what makes normalized tail terms vanish and step ratios summable.
--
--   **Formalization Note** "Sufficiently large" is the filter `atTop` on $\mathbb{N}$, and the conclusion is `Tendsto (fun n => F (n+1) - F n) atTop atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean#L197-L212

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
variable {F : ℕ → ℝ}

theorem OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Tendsto (fun n => F (n+1) - F n) atTop atTop := by sorry
