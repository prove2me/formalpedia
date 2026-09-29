-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_exp_concave_approx_lower_bound
-- name    : LogRegretOCO.FTAL.exp_concave_approx_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:38:57.349525+00:00
-- url     : https://prove2.me/theorems/cfdb3b3f-6c1a-4f41-a263-e0f6d85a7b5f
-- title:
--   Lemma 3 — exp-concave functions lie above a gradient paraboloid
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be convex with $\|x - y\| \le D$ for all $x, y \in P$, where $D > 0$. Let $f$ be a real function, differentiable at every point of $P$, with $\|\nabla f(x)\| \le G$ for $x \in P$ ($G > 0$), and such that $x \mapsto \exp(-\alpha f(x))$ is concave on $P$ for some $\alpha > 0$. Then for every $\beta$ with $0 < \beta \le \tfrac12 \min\{\tfrac{1}{4GD}, \alpha\}$,
--
--   $$
--   f(x) \ge f(y) + \nabla f(y)^\top (x - y) + \frac{\beta}{2} (x - y)^\top \nabla f(y) \nabla f(y)^\top (x - y) \qquad \text{for all } x, y \in P.
--   $$
--
--   The lemma says that an exp-concave function with bounded gradients is bounded below, on the whole decision set, by a rank-one quadratic that touches it at $y$. This is what lets Follow the Approximate Leader replace each cost by its quadratic model without increasing the regret.
--
--   **Formalization Note** The quadratic term is written as $\frac{\beta}{2}\langle \nabla f(y), x - y\rangle^2$, which equals $\frac{\beta}{2}(x-y)^\top \nabla f(y)\nabla f(y)^\top(x-y)$. The paper states $\beta \le \frac12\min\{\cdot\}$; the hypothesis $\beta > 0$ is added because the proof divides by $\beta$ (at $\beta = 0$ the claim would be the tangent inequality for a convex function). $G > 0$ and $D > 0$ make $1/(4GD)$ meaningful (in Lean $1/0 = 0$). $f$ is a function on all of $\mathbb{R}^n$, differentiable at the points of $P$; the diameter is used only as an upper bound.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 177, Lemma 3

import Mathlib

namespace LogRegretOCO.FTAL
theorem exp_concave_approx_lower_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D G α β : ℝ)
    (hPconv : Convex ℝ P) (hD : 0 < D) (hG : 0 < G) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ0 : 0 < β) (hβ : β ≤ 1 / 2 * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + inner ℝ (gradient f y) (x - y) + β / 2 * (inner ℝ (gradient f y) (x - y)) ^ 2
        ≤ f x := by sorry
end LogRegretOCO.FTAL
