-- Prove2me | Theorems.Thm_NonlinCG_FRBound_lemma_3_1
-- name    : NonlinCG.FRBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:43:54.644981+00:00
-- url     : https://prove2.me/theorems/82dfc28f-d6c8-4ae1-940c-8f34e9788287
-- title:
--   Lemma 3.1 — with $|\beta_k| \le \beta_k^{FR}$ and (2.17), $\sigma_2 < 1/2$, the directions are descent directions satisfying (3.2)
-- statement:
--   Let $f$ satisfy Assumptions 2.1 at $x_1$. Consider a method of the form (1.2)–(1.3), $d_1 = -g_1$, $d_k = -g_k + \beta_k d_{k-1}$ ($k \ge 2$), $x_{k+1} = x_k + \alpha_k d_k$ with $\alpha_k > 0$, in which every $\beta_k$ satisfies
--   $$|\beta_k| \le \beta_k^{FR} = \frac{\|g_k\|^2}{\|g_{k-1}\|^2}\qquad (k \ge 2) \tag{3.1}$$
--   and every steplength satisfies condition (2.17), $|\langle g(x_k + \alpha_k d_k), d_k\rangle| \le -\sigma_2\langle g_k, d_k\rangle$, with $0 < \sigma_2 < \tfrac12$. Suppose no gradient $g_k$ vanishes. Then every $d_k$ is a descent direction, $\langle g_k, d_k\rangle < 0$, and for every $k \ge 1$
--   $$-\sum_{j=0}^{k-1}\sigma_2^j \;\le\; \frac{\langle g_k, d_k\rangle}{\|g_k\|^2} \;\le\; -2 + \sum_{j=0}^{k-1}\sigma_2^j . \tag{3.2}$$
--
--   At $k = 1$ all three terms equal $-1$. Since $\sum_j \sigma_2^j < 1/(1-\sigma_2) < 2$, the upper bound gives the sufficient descent condition (2.18), and the two bounds control the growth of $\|d_k\|$ in the proof of Theorem 3.2.
--
--   **Formalization Note** The paper does not state $g_k \ne 0$; it divides by $\|g_k\|^2$ in (3.2) and calls $d_k$ a descent direction, which is impossible when $g_k = 0$, so we assume $g_k \ne 0$ for all $k \ge 1$. Only condition (2.17) is assumed, as in the paper ("the Wolfe condition (2.17)"), with the range $0 < \sigma_2$ from (2.17). The paper's standing assumption (1.1) "f is smooth" is taken as global $C^1$. Indices start at $1$; $\sum_{j=0}^{k-1}$ is a sum over $j < k$. The finite-dimensional real inner product space and positive steplengths are as in the definition file.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 7, Lemma 3.1, (3.2); (3.1) on p. 6

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.FRBound

/-- Lemma 3.1 (Gilbert–Nocedal, INRIA RR-1268, p. 7): for a method (1.2)–(1.3) with
`|β_k| ≤ β_k^{FR}` (3.1) for `k ≥ 2` and steplengths satisfying (2.17) with `0 < σ₂ < 1/2`, every
`d_k` is a descent direction and
`−Σ_{j=0}^{k−1} σ₂^j ≤ ⟨g_k, d_k⟩/‖g_k‖² ≤ −2 + Σ_{j=0}^{k−1} σ₂^j` for `k ≥ 1` (3.2).
The hypothesis `g_k ≠ 0` is implicit in the paper, which divides by `‖g_k‖²`. -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E)
    (σ₂ : ℝ) (hA : Assumptions21 f (x 1)) (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1,
      |inner ℝ (gradient f (x k + α k • d k)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k))
    (hg : ∀ k ≥ 1, g f x k ≠ 0) :
    ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0 ∧
      -(∑ j ∈ Finset.range k, σ₂ ^ j) ≤ inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ∧
      inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ≤ -2 + ∑ j ∈ Finset.range k, σ₂ ^ j := by sorry

end NonlinCG.FRBound
