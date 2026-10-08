-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_exp_concave_iff_hessian_v2
-- name    : OnlineConvexOpt.SecondOrder.exp_concave_iff_hessian_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:17.292493+00:00
-- url     : https://prove2.me/theorems/b3885d02-fec5-4ac9-a6cf-87df644a9c7d
-- title:
--   Lemma 4.2 — Hessian characterization of pointwise exp-concavity (with $\alpha>0$)
-- statement:
--   **Statement (Lemma 4.2).** Let $\alpha>0$, let $E$ be a real inner-product space, and let $f:E\to\mathbb R$ be twice differentiable at $x$. Then $f$ is $\alpha$-exp-concave at $x$ — i.e. $g(y)=e^{-\alpha f(y)}$ is concave to second order at $x$ (`IsExpConcaveAt`) — if and only if
--   $$\nabla^2 f(x)\succeq\alpha\,\nabla f(x)\nabla f(x)^\top,\qquad\text{i.e.}\qquad \forall v,\ v^\top\nabla^2f(x)v\ \ge\ \alpha\,(\nabla f(x)^\top v)^2 .$$
--
--   **Formalization Note.** The retired statement omitted the chapter's standing convention $\alpha>0$ (Definition 4.1's exp-concavity parameter is positive): for $\alpha=0$ the left side is always true while the right side says $\nabla^2f(x)\succeq0$, and for $\alpha<0$ the equivalence also fails. The hypothesis `hα : 0 < α` is added; nothing else changes. $v^\top\nabla^2f(x)v$ is the iterated Fréchet derivative `(fderiv ℝ (fderiv ℝ f) x) v v`, $\nabla f(x)^\top v$ the differential `(fderiv ℝ f x) v`, and `ContDiffAt ℝ 2 f x` renders "twice differentiable".
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 59, Lemma 4.2 (PDF p. 81)

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 4.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 59, PDF p. 81). For an exp-concavity parameter `α > 0`, a
twice-differentiable function `f : E → ℝ` is `α`-exp-concave at `x` (`IsExpConcaveAt`, the
pointwise Hessian formulation of `g(y) = exp(-α f(y))` being concave to second order at `x`) if
and only if `∇²f(x) ⪰ α∇f(x)∇f(x)^⊤`. The matrix inequality is stated as a comparison of the
two quadratic forms it induces: for every direction `v`, `v^⊤∇²f(x)v ≥ α(∇f(x)^⊤v)^2`, where
`v^⊤∇²f(x)v` is the iterated Fréchet derivative `(fderiv ℝ (fderiv ℝ f) x) v v` and
`∇f(x)^⊤v` is the differential `(fderiv ℝ f x) v`.

Corrected version: the retired statement omitted the chapter's standing convention `α > 0`
(Definition 4.1's exp-concavity parameter is positive; the Hessian of `exp(-αf)` is
`exp(-αf)(α²∇f∇f^⊤ - α∇²f)`, and dividing by `α` reverses or kills the inequality for
`α ≤ 0`). -/
theorem exp_concave_iff_hessian_v2 (α : ℝ) (hα : 0 < α) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by sorry

end OnlineConvexOpt.SecondOrder
