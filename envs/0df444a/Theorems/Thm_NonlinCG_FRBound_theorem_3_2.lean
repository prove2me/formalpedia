-- Prove2me | Theorems.Thm_NonlinCG_FRBound_theorem_3_2
-- name    : NonlinCG.FRBound.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:43:43.49401+00:00
-- url     : https://prove2.me/theorems/ee790975-7a46-4224-b097-3a51a09ddfb7
-- title:
--   Theorem 3.2 — methods with $|\beta_k| \le \beta_k^{FR}$ under strong Wolfe with $0 < \sigma_1 < \sigma_2 < 1/2$ have $\liminf \|g_k\| = 0$
-- statement:
--   Let $f : E \to \mathbb R$ be continuously differentiable on a finite-dimensional real inner product space and satisfy Assumptions 2.1 at the starting point $x_1$: the level set $\mathcal L = \{x : f(x) \le f(x_1)\}$ is bounded, and on an open neighbourhood of $\mathcal L$ the gradient $g$ is Lipschitz continuous. Consider any method of the form
--   $$d_1 = -g_1,\qquad d_k = -g_k + \beta_k d_{k-1}\ (k \ge 2),\qquad x_{k+1} = x_k + \alpha_k d_k\ (k\ge 1), \tag{1.2–1.3}$$
--   where the scalars $\beta_k$ are arbitrary subject to
--   $$|\beta_k| \le \beta_k^{FR} = \frac{\|g_k\|^2}{\|g_{k-1}\|^2}\qquad (k \ge 2), \tag{3.1}$$
--   and each steplength $\alpha_k > 0$ satisfies the strong Wolfe conditions with $0 < \sigma_1 < \sigma_2 < \tfrac12$:
--   $$f(x_k + \alpha_k d_k) \le f(x_k) + \sigma_1\alpha_k\langle g_k, d_k\rangle,\qquad |\langle g(x_k + \alpha_k d_k), d_k\rangle| \le -\sigma_2\langle g_k, d_k\rangle. \tag{2.16–2.17}$$
--   Then
--   $$\liminf_{k\to\infty}\|g_k\| = 0 .$$
--
--   The Fletcher–Reeves method ($\beta_k = \beta_k^{FR}$, Al-Baali 1985) and the hybrid Polak–Ribière/Fletcher–Reeves method (3.7) are instances. The bound $\sigma_2 < \tfrac12$ is needed for the result (p. 6).
--
--   **Formalization Note** The paper's standing assumption (1.1) "f is smooth" is taken as global $C^1$, in addition to Assumptions 2.1 (which ask for $C^1$ and a Lipschitz gradient only near $\mathcal L$). Steplengths are positive, as in the paper's line searches (p. 4). No hypothesis $g_k \ne 0$ is added: the paper does not assume it in §3, and if some $g_{k-1} = 0$ then Lean's division gives $\beta_k^{FR} = 0$, forcing $\beta_k = 0$ (a restart). The scalars $\beta_k$ are a free sequence constrained only by (3.1); the Zoutendijk condition is not assumed (it follows from Theorem 2.1). $\liminf\|g_k\| = 0$ is stated as: for every $\varepsilon > 0$ and every $K$ some $k \ge K$ has $\|g_k\| < \varepsilon$. Indices start at $1$; index $0$ of the sequences is unused.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 8, Theorem 3.2; (3.1) on p. 6

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.FRBound

/-- Theorem 3.2 (Gilbert–Nocedal, INRIA RR-1268, p. 8): under Assumptions 2.1, any method of the
form (1.2)–(1.3) whose `β_k` satisfies `|β_k| ≤ β_k^{FR}` (3.1) for all `k ≥ 2` and whose
steplengths satisfy the strong Wolfe conditions (2.16)–(2.17) with `0 < σ₁ < σ₂ < 1/2` has
`liminf_{k→∞} ‖g_k‖ = 0`. -/
theorem theorem_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1)) (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1, StrongWolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    LiminfGradZero f x := by sorry

end NonlinCG.FRBound
