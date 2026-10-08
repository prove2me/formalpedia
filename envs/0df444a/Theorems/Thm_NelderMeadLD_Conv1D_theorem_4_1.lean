-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_theorem_4_1
-- name    : NelderMeadLD.Conv1D.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:24.324024+00:00
-- url     : https://prove2.me/theorems/0f4c6e19-6ea3-42b3-ab9e-f7c6445a3ab7
-- title:
--   Theorem 4.1, p. 125 — in dimension 1 with ρχ ≥ 1, both endpoints of the Nelder–Mead interval converge to x_min
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex with bounded level sets $\{x : f(x) \le \mu\}$, and let $x_{\min}$ be its minimizer. Run the Nelder–Mead method (Algorithm NM) in dimension $1$ with parameters satisfying
--   $$\rho > 0,\quad \chi > 1,\quad \chi > \rho,\quad \rho\chi \ge 1,\quad 0 < \gamma < 1$$
--   (and a shrink coefficient $0 < \sigma < 1$), from a nondegenerate initial interval $\Delta_0 = (x_1^{(0)}, x_2^{(0)})$, $x_1^{(0)} \ne x_2^{(0)}$, ordered so that $f(x_1^{(0)}) \le f(x_2^{(0)})$. Then both endpoints of the Nelder–Mead interval converge to the minimizer:
--   $$\lim_{k\to\infty} x_1^{(k)} = x_{\min} \quad\text{and}\quad \lim_{k\to\infty} x_2^{(k)} = x_{\min}.$$
--
--   This is the global convergence theorem for the Nelder–Mead method on strictly convex functions of one variable; together with the remark that convergence can fail when $\rho\chi < 1$, it shows that $\rho\chi \ge 1$ is the right condition.
--
--   **Formalization Note** The theorem does not mention $\sigma$, because no shrink step occurs for strictly convex $f$ (Lemma 3.5); $\sigma$ is still a parameter of the algorithm and satisfies the standing condition $0 < \sigma < 1$ of (2.1). The pair `p : ℝ × ℝ` stores $(x_1, x_2)$ with $x_1$ the best vertex; the initial ordering is a hypothesis, with ties in either order allowed.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 125, Theorem 4.1

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem theorem_4_1 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    Tendsto (fun k => (run f ρ χ γ σ p0 k).1) atTop (𝓝 xmin) ∧
      Tendsto (fun k => (run f ρ χ γ σ p0 k).2) atTop (𝓝 xmin) := by sorry

end NelderMeadLD.Conv1D
