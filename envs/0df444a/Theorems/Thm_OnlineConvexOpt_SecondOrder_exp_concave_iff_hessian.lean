-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_exp_concave_iff_hessian
-- name    : OnlineConvexOpt.SecondOrder.exp_concave_iff_hessian
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:31:32.17331+00:00
-- url     : https://prove2.me/theorems/20b9a7fc-b7f0-4849-9ddf-a2afe9481df1
-- title:
--   Lemma 4.2 — exp-concavity via the Hessian
-- statement:
--   This is the Hessian characterization of pointwise exp-concavity referenced in the
--   definitions above. Let $f : E \to \mathbb{R}$ be twice differentiable at a point $x$ of a
--   real inner-product space $E$, and let $\alpha > 0$. Then $f$ is $\alpha$-exp-concave at $x$
--   — i.e. $g(y) = e^{-\alpha f(y)}$ is concave to second order at $x$ — if and only if
--   $$
--   \nabla^2 f(x) \succeq \alpha\, \nabla f(x)\, \nabla f(x)^\top ,
--   $$
--   meaning that for every direction $v \in E$,
--   $$
--   v^\top \nabla^2 f(x)\, v \;\ge\; \alpha \bigl(\nabla f(x)^\top v\bigr)^2 .
--   $$
--   Since $\nabla f(x)\nabla f(x)^\top$ has rank one, this says the Hessian of $f$ need only
--   dominate $\alpha$ times the outer product of the gradient with itself: strong curvature
--   exactly along the gradient direction, unlike $\alpha$-strong convexity, which demands
--   $\nabla^2 f(x) \succeq \alpha I$ in every direction. This is the precise sense in which
--   exp-concave functions form a strictly larger class than strongly convex, Lipschitz
--   functions, and it is what allows functions with a low-rank Hessian, such as the negative
--   log-loss $-\log(r^\top x)$ of online portfolio selection, to be exp-concave.
--
--   **Formalization Note** $v^\top\nabla^2f(x)v$ is the iterated Fréchet derivative
--   `(fderiv ℝ (fderiv ℝ f) x) v v`, and $\nabla f(x)^\top v$ is the differential
--   `(fderiv ℝ f x) v`; both sides avoid naming a gradient vector via Riesz representation.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 59, PDF p. 81, Lemma 4.2

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 4.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 59, PDF p. 81). A twice-differentiable function `f : E → ℝ` is
`α`-exp-concave at `x` (`IsExpConcaveAt`, the pointwise Hessian formulation of `g(y) =
exp(-α f(y))` being concave to second order at `x`) if and only if `∇²f(x) ⪰ α∇f(x)∇f(x)^⊤`.
The matrix inequality is stated as a comparison of the two quadratic forms it induces: for every
direction `v`, `v^⊤∇²f(x)v ≥ α(∇f(x)^⊤v)^2`, where `v^⊤∇²f(x)v` is the iterated Fréchet
derivative `(fderiv ℝ (fderiv ℝ f) x) v v` and `∇f(x)^⊤v` is the differential `(fderiv ℝ f x) v`.
-/
theorem exp_concave_iff_hessian (α : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by sorry

end OnlineConvexOpt.SecondOrder
