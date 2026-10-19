-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_ConvexEnvelope_convex
-- name    : OAI.BackwardIntertwiners.ConvexEnvelope.convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:58.21756+00:00
-- url     : https://prove2.me/theorems/0f7ef5b1-9480-452e-a81a-f5b08e0ed6f4
-- title:
--   The discrete convex envelope of an obstacle is discretely convex
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Fix a set $I\subseteq\mathbb{N}$ (the obstacle set) and a function $f:\mathbb{N}\to\mathbb{R}$ (the obstacle), and let
--   $$\mathcal M(I,f)=\bigl\{F:\mathbb{N}\to\mathbb{R}\ :\ F(0)=0,\ F\text{ discretely convex},\ F(n)\le f(n)\text{ for all }n\in I\bigr\}$$
--   be the set of normalized convex minorants of $f$ on $I$. The *convex envelope* of $f$ on $I$ is the pointwise supremum
--   $$\operatorname{Env}_{I,f}(n)=\sup\{F(n):F\in\mathcal M(I,f)\}\qquad(n\in\mathbb{N}).$$
--
--   Assume that $I$ is unbounded (for every $n\in\mathbb{N}$ there is $k\in I$ with $k>n$) and that $\mathcal M(I,f)\neq\varnothing$. Then $\operatorname{Env}_{I,f}$ is discretely convex:
--   $$\operatorname{Env}_{I,f}(n+1)-\operatorname{Env}_{I,f}(n)\le\operatorname{Env}_{I,f}(n+2)-\operatorname{Env}_{I,f}(n+1)\qquad\text{for all }n\in\mathbb{N}.$$
--
--   Since every minorant vanishes at $0$ and lies below $f$ on $I$, so does the envelope; with this theorem the envelope is therefore itself an element of $\mathcal M(I,f)$, namely the largest one. This is the starting point for the contact property of the envelope and for the convex envelopes of coefficient sequences used in the project's support estimates for weighted sequences.
--
--   **Formalization Note** The supremum is Mathlib's `sSup` on $\mathbb{R}$, which returns $0$ for empty or unbounded sets; under the two hypotheses every set $\{F(n):F\in\mathcal M(I,f)\}$ is nonempty and bounded above, so $\operatorname{Env}_{I,f}(n)$ is a genuine supremum. Discrete convexity is `DiscreteConvex F`, monotonicity of $n\mapsto F(n+1)-F(n)$; $\mathcal M(I,f)$ is `convexMinorants I f` and $\operatorname{Env}_{I,f}$ is `convexEnvelope I f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean#L127-L139

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

include hunbounded hne in
theorem OAI.BackwardIntertwiners.ConvexEnvelope.convex : DiscreteConvex (convexEnvelope I f) := by sorry
