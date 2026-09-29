-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_step_exists
-- name    : NonmonotoneLS.Global.step_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:21:26.75282+00:00
-- url     : https://prove2.me/theorems/852c39ae-8473-4723-96e4-cf1f64c41a37
-- title:
--   Lemma 1.1 (existence) — a nonmonotone Wolfe step and an Armijo exponent exist
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and bounded from below, and let the NLSA parameters be fixed. Let $x, d \in \mathbb{R}^n$ with $\nabla f(x) d < 0$, and let $C$ be a reference value with $f(x) \le C$. Then
--
--   1. there is a step $\alpha > 0$ satisfying the nonmonotone Wolfe conditions (1.4)–(1.5) at $x$ with direction $d$ and reference value $C$; and
--   2. for every trial step $\bar\alpha > 0$ there is a largest integer $h$ such that
--   $$f(x + \bar\alpha\rho^h d) \le C + \delta \bar\alpha\rho^h \nabla f(x) d \quad\text{and}\quad \bar\alpha \rho^h \le \mu,$$
--   so that $\alpha = \bar\alpha\rho^h$ satisfies the nonmonotone Armijo conditions.
--
--   Along a run, the hypothesis $f(x_k) \le C_k$ is the first part of Lemma 1.1; together the two parts show that the line search update of the algorithm can always be carried out.
--
--   **Formalization Note.** The statement is pointwise in $(x, d, C)$. The paper's "there exists $\alpha_k$ satisfying either the Wolfe or Armijo conditions" is read, as in its proof ("$\alpha_k$ can be chosen to satisfy either the Wolfe or the Armijo line search conditions"), as: each rule can be satisfied; so both conclusions are stated, the Armijo one for every trial step.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1045, Lemma 1.1 (second sentence)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 1.1, second sentence (p. 1045): if `∇f(x) d < 0`, `f` is bounded from below and the
reference value satisfies `f(x) ≤ C`, then a nonmonotone Wolfe step exists, and for every trial
step `ᾱ > 0` there is a largest integer `h` with `ᾱ ρ^h` satisfying (1.4) and `ᾱ ρ^h ≤ μ`. -/
theorem step_exists {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : f x ≤ C)
    (hdesc : ⟪gradient f x, d⟫_ℝ < 0) :
    (∃ α : ℝ, Shared.IsWolfeStep p f x d C α) ∧
      ∀ αbar : ℝ, 0 < αbar → ∃ h : ℤ, IsGreatest (Shared.armijoAdmissible p f x d C αbar) h := by sorry

end NonmonotoneLS.Global
