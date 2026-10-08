-- Prove2me | Theorems.Thm_NonlinCG_FRBound_cos_theta_bounds
-- name    : NonlinCG.FRBound.cos_theta_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:43:34.666987+00:00
-- url     : https://prove2.me/theorems/74e619dd-59f0-44b4-a197-e71770deadcb
-- title:
--   §3, (3.5) — $c_1\|g_k\|/\|d_k\| \le \cos\theta_k \le c_2\|g_k\|/\|d_k\|$ for methods with $|\beta_k| \le \beta_k^{FR}$
-- statement:
--   Under the hypotheses of Lemma 3.1 — Assumptions 2.1, a method of the form (1.2)–(1.3) with $|\beta_k| \le \beta_k^{FR}$ for $k \ge 2$, steplengths satisfying (2.17) with $0 < \sigma_2 < \tfrac12$, and no vanishing gradient — there are positive constants $c_1$ and $c_2$ such that for every $k \ge 1$
--   $$c_1\,\frac{\|g_k\|}{\|d_k\|} \;\le\; \cos\theta_k \;\le\; c_2\,\frac{\|g_k\|}{\|d_k\|}, \tag{3.5}$$
--   where $\cos\theta_k = -\langle g_k, d_k\rangle/(\|g_k\|\,\|d_k\|)$ (2.1).
--
--   Thus, for the Fletcher–Reeves method or any method with $|\beta_k| \le \beta_k^{FR}$, $\cos\theta_k$ is proportional to $\|g_k\|/\|d_k\|$. The left inequality, combined with the Zoutendijk condition, is what turns a bound on the growth of $\|d_k\|$ into convergence in Theorem 3.2.
--
--   **Formalization Note** The paper states existence of $c_1, c_2$; its derivation from (2.1) and (3.2) gives $c_1 = (1-2\sigma_2)/(1-\sigma_2)$ and $c_2 = 1/(1-\sigma_2)$, but the statement asserts existence only. The constants may depend on $\sigma_2$ but are uniform in $k$. The hypothesis $g_k \ne 0$ is that of Lemma 3.1 (the paper divides by $\|g_k\|$). Global $C^1$ from (1.1), finite-dimensional real inner product space, indices from $1$, positive steplengths, as in the definition file.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, §3, (3.5), p. 7

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.FRBound

/-- Display (3.5) (Gilbert–Nocedal, INRIA RR-1268, §3, p. 7): under the hypotheses of Lemma 3.1
there are positive constants `c₁, c₂` with `c₁ ‖g_k‖/‖d_k‖ ≤ cos θ_k ≤ c₂ ‖g_k‖/‖d_k‖` for all
`k ≥ 1`. -/
theorem cos_theta_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E)
    (σ₂ : ℝ) (hA : Assumptions21 f (x 1)) (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1,
      |inner ℝ (gradient f (x k + α k • d k)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k))
    (hg : ∀ k ≥ 1, g f x k ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k ≥ 1,
      c₁ * (‖g f x k‖ / ‖d k‖) ≤ cosTheta f x d k ∧
      cosTheta f x d k ≤ c₂ * (‖g f x k‖ / ‖d k‖) := by sorry

end NonlinCG.FRBound
