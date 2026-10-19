-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_ConvexEnvelope_contact
-- name    : OAI.BackwardIntertwiners.ConvexEnvelope.contact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:14:28.125389+00:00
-- url     : https://prove2.me/theorems/0f7627d1-ae17-4286-be2d-c041b9b88012
-- title:
--   Contact property: where the discrete convex envelope bends strictly, it touches the obstacle
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Fix a set $I\subseteq\mathbb{N}$ (the obstacle set) and a function $f:\mathbb{N}\to\mathbb{R}$ (the obstacle), and let
--   $$\mathcal M(I,f)=\bigl\{F:\mathbb{N}\to\mathbb{R}\ :\ F(0)=0,\ F\text{ discretely convex},\ F(n)\le f(n)\text{ for all }n\in I\bigr\}$$
--   be the set of normalized convex minorants of $f$ on $I$. The *convex envelope* of $f$ on $I$ is the pointwise supremum
--   $$\operatorname{Env}_{I,f}(n)=\sup\{F(n):F\in\mathcal M(I,f)\}\qquad(n\in\mathbb{N}).$$
--
--   Assume that $I$ is unbounded (for every $n\in\mathbb{N}$ there is $k\in I$ with $k>n$) and that $\mathcal M(I,f)\neq\varnothing$. If $n\in\mathbb{N}$ is such that the second difference of the envelope at $n$ is strictly positive,
--   $$\operatorname{Env}_{I,f}(n+2)-2\operatorname{Env}_{I,f}(n+1)+\operatorname{Env}_{I,f}(n)>0,$$
--   then $n+1\in I$ and $\operatorname{Env}_{I,f}(n+1)=f(n+1)$.
--
--   In words: the envelope can have a strict corner only at a point of the obstacle set, and there it coincides with the obstacle. When the obstacle is $f(n)=-\log|d_n|$ for a coefficient sequence $(d_n)$, this says that the bound $|d_n|\le e^{-\operatorname{Env}(n)}$ is attained at every strict corner, which is how exact-size coefficients are produced in the project's correlation estimates.
--
--   **Formalization Note** The supremum is Mathlib's `sSup` on $\mathbb{R}$, which returns $0$ for empty or unbounded sets; under the two hypotheses every set $\{F(n):F\in\mathcal M(I,f)\}$ is nonempty and bounded above, so $\operatorname{Env}_{I,f}(n)$ is a genuine supremum. Discrete convexity is `DiscreteConvex F`, monotonicity of $n\mapsto F(n+1)-F(n)$; $\mathcal M(I,f)$ is `convexMinorants I f` and $\operatorname{Env}_{I,f}$ is `convexEnvelope I f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean#L151-L188

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
theorem OAI.BackwardIntertwiners.ConvexEnvelope.contact (n : ℕ)
    (hgap : 0 < convexEnvelope I f (n+2) - 2 * convexEnvelope I f (n+1) +
      convexEnvelope I f n) :
    n+1 ∈ I ∧ convexEnvelope I f (n+1) = f (n+1) := by sorry
