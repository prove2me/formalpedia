-- Prove2me | Theorems.Thm_NonlinCG_PropStar_theorem_4_3
-- name    : NonlinCG.PropStar.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:30.346687+00:00
-- url     : https://prove2.me/theorems/772b80c9-c349-4489-951f-f04afedb2d77
-- title:
--   Theorem 4.3 — conjugate gradient methods with β_k ≥ 0 and Property (*) satisfy liminf ‖g_k‖ = 0
-- statement:
--   Let $f : E \to \mathbb R$ satisfy Assumptions 2.1 at the starting point $x_1$: the level set $\mathcal L = \{x : f(x) \le f(x_1)\}$ is bounded and, on an open neighbourhood of $\mathcal L$, $f$ is continuously differentiable with an $L$-Lipschitz gradient. Consider a run of the conjugate gradient iteration
--
--   $$d_1 = -g_1, \qquad d_k = -g_k + \beta_k d_{k-1}\ (k \ge 2), \qquad x_{k+1} = x_k + \alpha_k d_k,\ \alpha_k > 0,$$
--
--   with $g_k = \nabla f(x_k) \ne 0$ for all $k$, and with the following three properties:
--
--   1. $\beta_k \ge 0$ for all $k$;
--   2. the line search keeps the iterates in $\mathcal L$ (4.4), satisfies the Zoutendijk condition $\sum_k \cos^2\theta_k\|g_k\|^2 < \infty$ (2.7), and the sufficient descent condition $\langle g_k, d_k\rangle \le -\sigma_3 \|g_k\|^2$ for all $k\ge1$ (4.1), with $0 < \sigma_3 \le 1$;
--   3. the method has Property (\*): whenever $0 < \gamma \le \|g_k\| \le \bar\gamma$ for all $k$, there are $b > 1$ and $\lambda > 0$ with $|\beta_k| \le b$ and $\|x_k - x_{k-1}\| \le \lambda \Rightarrow |\beta_k| \le 1/(2b)$ for all $k \ge 2$.
--
--   Then
--
--   $$\liminf_{k \to \infty} \|g_k\| = 0.$$
--
--   The theorem covers every conjugate gradient method whose $\beta_k$ is nonnegative and bounded and becomes small after small steps, with any line search having the three properties of (ii); in particular it applies to the Polak–Ribière method with $\beta_k$ truncated at zero (Corollary 4.4), and to practical (inexact) as well as ideal line searches.
--
--   **Formalization Note** The paper's standing assumption for §4, "we assume that convergence does not occur in a finite number of steps, i.e., $g_k \ne 0$ for all $k$" (p. 11), is a hypothesis. Global continuous differentiability of $f$ (the paper's "$f$ is smooth", (1.1)) is assumed in addition to Assumptions 2.1. Steplengths are positive, as in the paper's line searches (p. 4). Sequences are indexed from $1$, and $\beta_k$ is a free sequence constrained only by the hypotheses. The Zoutendijk sum is written $\sum_k \langle g_k,d_k\rangle^2/\|d_k\|^2$. $\liminf \|g_k\| = 0$ is stated as: for every $\varepsilon > 0$ and $K$ there is $k \ge K$ with $\|g_k\| < \varepsilon$.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 15, Theorem 4.3; standing assumption g_k ≠ 0 of §4, p. 11

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

namespace NonlinCG.PropStar

/-- Theorem 4.3 (p. 15). Under Assumptions 2.1, for a run of (1.2)–(1.3) with (i) `β_k ≥ 0`,
(ii) a line search satisfying (4.4), the Zoutendijk condition (2.7) and the sufficient descent
condition (4.1), and (iii) Property (*), `liminf ‖g_k‖ = 0`. As throughout §4 (p. 11), `g_k ≠ 0`
for all `k`. -/
theorem theorem_4_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hg : ∀ k ≥ 1, NonlinCG.FRBound.g f x k ≠ 0)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x) :
    NonlinCG.FRBound.LiminfGradZero f x := by sorry

end NonlinCG.PropStar
