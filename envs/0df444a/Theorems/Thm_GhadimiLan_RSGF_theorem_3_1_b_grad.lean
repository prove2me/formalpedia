-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_theorem_3_1_b_grad
-- name    : GhadimiLan.RSGF.theorem_3_1_b_grad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:30.939983+00:00
-- url     : https://prove2.me/theorems/508c53b2-6418-4930-97e1-93acdf8c7b9b
-- title:
--   Theorem 3.1 b), (3.6), p. 15 — ‖∇f_µ(x) − ∇f(x)‖ ≤ (µ/2)L(n+3)^{3/2} for f ∈ C^{1,1}_L
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable with $L$-Lipschitz gradient, $L \ge 0$. For $\mu > 0$ let
--   $$
--   f_\mu(x) = \mathbb E_u[f(x+\mu u)]
--   $$
--   be its Gaussian smoothing (3.3), where $u$ is an $n$-dimensional standard Gaussian vector. Then for every $x \in \mathbb R^n$,
--   $$
--   \|\nabla f_\mu(x) - \nabla f(x)\| \le \frac{\mu}{2}\, L\,(n+3)^{3/2}.
--   $$
--
--   The bound measures how far the gradient of the smoothed function is from the true gradient. In the analysis of the RSGF method it converts bounds on $\|\nabla f_\mu\|$ into bounds on $\|\nabla f\|$, through (3.8)–(3.9). The paper attributes it to Nesterov and gives no proof.
--
--   **Formalization Note** The smoothing parameter $\mu$ is `μs` in Lean, and $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so the $n$ in $(n+3)$ is the dimension.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 3.1 b), Eq. (3.6), p. 15

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Theorem 3.1 b), Eq. (3.6) (Ghadimi & Lan, arXiv:1309.5549v1, p. 15; due to Nesterov): for
`f ∈ C^{1,1}_L(ℝⁿ)` and smoothing parameter `μs > 0` (the paper's `µ`), the gradient of the
Gaussian smoothing `f_µ` of (3.3) satisfies `‖∇f_µ(x) − ∇f(x)‖ ≤ (µ/2) L (n+3)^{3/2}` for every
`x ∈ ℝⁿ`. -/
theorem theorem_3_1_b_grad {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μs : ℝ) (hμs : 0 < μs) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (RandomGradFree.Shared.smoothing f μs) x - gradient f x‖ ≤
      μs / 2 * L * ((n : ℝ) + 3) ^ ((3 : ℝ) / 2) := by sorry

end GhadimiLan.RSGF
