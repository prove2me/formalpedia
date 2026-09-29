-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_exp_concave_quadratic_lower_bound
-- name    : LogRegretOCO.ONS.exp_concave_quadratic_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:35:01.064762+00:00
-- url     : https://prove2.me/theorems/fdf9119c-d431-4b20-9043-0c13582f9e35
-- title:
--   Lemma 3 — exp-concave functions admit a quadratic lower bound built from the gradient
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ have diameter at most $D>0$, i.e. $\|x-y\|\le D$ for all $x,y\in\mathcal P$. Let $f:\mathbb R^n\to\mathbb R$ be differentiable at every point of $\mathcal P$ with $\|\nabla f(x)\|\le G$ for all $x\in\mathcal P$, where $G>0$, and suppose that $x\mapsto\exp(-\alpha f(x))$ is concave on $\mathcal P$. Then for every $\beta$ with
--   $$
--   0<\beta\le\tfrac12\min\Big\{\frac1{4GD},\,\alpha\Big\}
--   $$
--   and all $x,y\in\mathcal P$,
--   $$
--   f(x)\ \ge\ f(y)+\nabla f(y)^\top(x-y)+\frac\beta2\,(x-y)^\top\nabla f(y)\nabla f(y)^\top(x-y).
--   $$
--
--   The lemma replaces the Hessian in a second-order Taylor bound by the rank-one matrix $\nabla f(y)\nabla f(y)^\top$; this is what lets the Online Newton Step work from gradients alone. It gives the per-round inequality (3) of the proof of Theorem 2.
--
--   **Formalization Note** The quadratic term is written as $\beta/2\cdot(\nabla f(y)^\top(x-y))^2$, which equals $(x-y)^\top\nabla f(y)\nabla f(y)^\top(x-y)$. The hypotheses $G>0$, $D>0$ are the non-degeneracy the formula $1/(4GD)$ presupposes (in Lean $1/0=0$). The hypothesis $\beta>0$ is added: the paper's proof divides by $\beta$, and it forces $\alpha>0$, which is part of the paper's definition of $\alpha$-exp-concavity. The diameter is used only as the upper bound $\|x-y\|\le D$, which makes the statement slightly more general. The paper's standing assumptions that $f$ is convex and twice differentiable are not needed (convexity follows from exp-concavity) and are omitted.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 177, Lemma 3

import Mathlib
open scoped RealInnerProductSpace

namespace LogRegretOCO.ONS

/-- Lemma 3 (Hazan–Agarwal–Kale 2007, p. 177). Let `P` have diameter at most `D`, let `f` be
differentiable at every point of `P` with `‖∇f(x)‖ ≤ G` there, and let `exp(−α f)` be concave on
`P`. Then for every `0 < β ≤ ½ min{1/(4GD), α}` and all `x, y ∈ P`,
`f(x) ≥ f(y) + ∇f(y)ᵀ(x − y) + (β/2) (x − y)ᵀ ∇f(y) ∇f(y)ᵀ (x − y)`.
`0 < G`, `0 < D` are the non-degeneracy the formula `1/(4GD)` presupposes; `0 < β` excludes the
degenerate step size (the proof divides by `β`). -/
theorem exp_concave_quadratic_lower_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (G D α β : ℝ) (hG : 0 < G) (hD : 0 < D)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ_pos : 0 < β) (hβ : β ≤ (1 / 2) * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + ⟪gradient f y, x - y⟫ + (β / 2) * ⟪gradient f y, x - y⟫ ^ 2 ≤ f x := by sorry

end LogRegretOCO.ONS
