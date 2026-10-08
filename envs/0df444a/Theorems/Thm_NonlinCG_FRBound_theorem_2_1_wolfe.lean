-- Prove2me | Theorems.Thm_NonlinCG_FRBound_theorem_2_1_wolfe
-- name    : NonlinCG.FRBound.theorem_2_1_wolfe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:43:56.738981+00:00
-- url     : https://prove2.me/theorems/c5af65f9-f332-4bab-ba2d-e00afbc25075
-- title:
--   Theorem 2.1 (i) — Zoutendijk: descent directions with Wolfe steps give $\sum_k \cos^2\theta_k\|g_k\|^2 < \infty$
-- statement:
--   Let $f$ satisfy Assumptions 2.1 at the starting point $x_1$: the level set $\mathcal L = \{x : f(x) \le f(x_1)\}$ is bounded and $f$ has a Lipschitz continuous gradient $g$ on an open neighbourhood of $\mathcal L$. Consider any iteration $x_{k+1} = x_k + \alpha_k d_k$, $k \ge 1$ (1.3), with arbitrary directions $d_k$, where each $d_k$ is a descent direction, $\langle g_k, d_k\rangle < 0$, and each positive steplength $\alpha_k$ satisfies the Wolfe conditions (2.4)–(2.5) with $0 < \sigma_1 < \sigma_2 < 1$:
--   $$f(x_k + \alpha_k d_k) \le f(x_k) + \sigma_1\alpha_k\langle g_k, d_k\rangle,\qquad \langle g(x_k + \alpha_k d_k), d_k\rangle \ge \sigma_2\langle g_k, d_k\rangle.$$
--   Then, with $\theta_k$ the angle between $-g_k$ and $d_k$,
--   $$\sum_{k \ge 1} \cos^2\theta_k\,\|g_k\|^2 < \infty .$$
--
--   This is the Zoutendijk condition (2.7), the basic tool of the paper's global convergence analysis: it is the only consequence of the line search that the proof of Theorem 3.2 uses besides the descent bounds.
--
--   **Formalization Note** The paper states (1.1) "f is smooth"; we assume $f$ is $C^1$ on the whole space, in addition to Assumptions 2.1. The steplengths are positive, as in the paper's definition of the Wolfe line search (p. 4). The sum is stated as summability of $\langle g_k, d_k\rangle^2/\|d_k\|^2$ over $k \ge 1$, which equals $\cos^2\theta_k\|g_k\|^2$ here because descent forces $g_k \ne 0$ and $d_k \ne 0$. The space is a finite-dimensional real inner product space; indices start at $1$. Part (ii) of the theorem (ideal line search) is a separate item.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 4, Theorem 2.1 (i)

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.FRBound

/-- Theorem 2.1 (i) (Gilbert–Nocedal, INRIA RR-1268, p. 4): under Assumptions 2.1, any iteration
`x_{k+1} = x_k + α_k d_k` (1.3) with positive steplengths, descent directions `d_k` and
steplengths satisfying the Wolfe conditions (2.4)–(2.5) with `0 < σ₁ < σ₂ < 1` satisfies the
Zoutendijk condition (2.7). The directions `d_k` are arbitrary, not necessarily (1.2). -/
theorem theorem_2_1_wolfe {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1))
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1)
    (hiter : ∀ k ≥ 1, 0 < α k ∧ x (k + 1) = x k + α k • d k)
    (hdesc : ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0)
    (hls : ∀ k ≥ 1, WolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    ZoutendijkCondition f x d := by sorry

end NonlinCG.FRBound
