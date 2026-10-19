-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_tail_term_tendsto
-- name    : OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:18:08.712786+00:00
-- url     : https://prove2.me/theorems/ba44c818-c8cf-47f1-b153-ad4841d7fbc5
-- title:
--   Normalized tail terms of a convex sequence with divergent increments tend to zero
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. For $F:\mathbb{N}\to\mathbb{R}$ and $q,k\in\mathbb{N}$, the *normalized tail term* is $T_F(q,k)=\exp\bigl(F(k+1)+F(q)-F(q+k+1)\bigr)$.
--
--   Let $F:\mathbb{N}\to\mathbb{R}$ be discretely convex with $F(n+1)-F(n)\to+\infty$. Then for every fixed $k\in\mathbb{N}$,
--   $$\lim_{q\to\infty}T_F(q,k)=\lim_{q\to\infty}\exp\bigl(F(k+1)+F(q)-F(q+k+1)\bigr)=0.$$
--
--   The exponent compares the growth $F(q+k+1)-F(q)$ of $F$ over a window of length $k+1$ starting at $q$ with the value $F(k+1)$; divergent increments make the far windows grow much faster. In the project these terms bound the far tails of correlation sums relative to their central term, and this termwise decay, combined with a summable majorant, shows that the total tail contribution becomes negligible as $q\to\infty$.
--
--   **Formalization Note** $T_F(q,k)$ is `normalizedTailTerm F q k`; no normalization $F(0)=0$ is needed here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean#L349-L365

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
variable {F : ℕ → ℝ}

theorem OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto (h : DiscreteConvex F)
    (hs : Tendsto (fun n => F (n+1) - F n) atTop atTop) (k : ℕ) :
    Tendsto (fun q => normalizedTailTerm F q k) atTop (𝓝 0) := by sorry
