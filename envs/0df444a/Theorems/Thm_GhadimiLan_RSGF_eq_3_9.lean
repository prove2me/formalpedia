-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_eq_3_9
-- name    : GhadimiLan.RSGF.eq_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:26.858978+00:00
-- url     : https://prove2.me/theorems/33a9a4e5-b7cd-4c86-97aa-69afd4ce07f7
-- title:
--   (3.8)–(3.9), p. 15 — ‖∇f(x)‖² ≤ 2‖∇f_µ(x)‖² + (µ²/2)L²(n+3)³ and its mirror
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable with $L$-Lipschitz gradient, $L \ge 0$, let $\mu > 0$, and let $f_\mu$ be the Gaussian smoothing (3.3). Then for every $x \in \mathbb R^n$:
--
--   1. (3.8)
--   $$
--   \|\nabla f_\mu(x)\|^2 \le 2\|\nabla f(x)\|^2 + \frac{\mu^2}{2} L^2 (n+3)^3 ;
--   $$
--   2. (3.9)
--   $$
--   \|\nabla f(x)\|^2 \le 2\|\nabla f_\mu(x)\|^2 + \frac{\mu^2}{2} L^2 (n+3)^3 .
--   $$
--
--   The paper derives both from (3.6). Inequality (3.9) turns the bound on $\sum_k \gamma_k \mathbb E\|\nabla f_\mu(x_k)\|^2$ obtained from (3.19) into a bound on $\mathbb E\|\nabla f(x_k)\|^2$. The proof of Theorem 3.2 cites it as "(3.8)".
--
--   **Formalization Note** The smoothing parameter $\mu$ is `μs` in Lean.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eqs. (3.8)–(3.9), p. 15

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Eqs. (3.8)–(3.9) (Ghadimi & Lan, arXiv:1309.5549v1, p. 15), consequences of (3.6): for
`f ∈ C^{1,1}_L(ℝⁿ)`, `μs > 0` (the paper's `µ`) and every `x`,
`‖∇f_µ(x)‖² ≤ 2‖∇f(x)‖² + (µ²/2) L² (n+3)³` (3.8) and `‖∇f(x)‖² ≤ 2‖∇f_µ(x)‖² + (µ²/2) L² (n+3)³` (3.9). -/
theorem eq_3_9 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μs : ℝ) (hμs : 0 < μs) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (RandomGradFree.Shared.smoothing f μs) x‖ ^ 2 ≤
        2 * ‖gradient f x‖ ^ 2 + μs ^ 2 / 2 * L ^ 2 * ((n : ℝ) + 3) ^ 3 ∧
      ‖gradient f x‖ ^ 2 ≤
        2 * ‖gradient (RandomGradFree.Shared.smoothing f μs) x‖ ^ 2 +
          μs ^ 2 / 2 * L ^ 2 * ((n : ℝ) + 3) ^ 3 := by sorry

end GhadimiLan.RSGF
