-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_lemma_1_2
-- name    : GlobalInexactNewton.Backtracking.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:40.58362+00:00
-- url     : https://prove2.me/theorems/9cded8ac-077f-4f92-b761-fefd41a68f5d
-- title:
--   Lemma 1.2 — uniform linearization error $\|F(z)-F(y)-F'(y)(z-y)\|\le\varepsilon\|z-y\|$ near $x$
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. For every $x\in E$ and $\varepsilon>0$ there is $\delta>0$ such that
--   $$\|F(z)-F(y)-F'(y)(z-y)\|\le\varepsilon\,\|z-y\|$$
--   whenever $\|y-x\|<\delta$ and $\|z-x\|<\delta$.
--
--   The derivative is taken at the base point $y$, not at the centre $x$. The lemma controls the error of the local linear model uniformly on a neighbourhood and is used to show that inexact Newton steps eventually give sufficient decrease.
--
--   **Formalization Note** $N_\delta(x)$ is the open ball of radius $\delta$ about $x$. Continuous differentiability is the paper's standing assumption (p. 395).
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), pp. 395–396, Lemma 1.2

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), pp. 395–396, Lemma 1.2: for any `x` and `ε > 0` there is `δ > 0`
such that `‖F(z) - F(y) - F'(y)(z - y)‖ ≤ ε ‖z - y‖` whenever `y, z ∈ N_δ(x)`.
Standing assumption (p. 395): `F` is continuously differentiable. -/
theorem lemma_1_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      ‖F z - F y - fderiv ℝ F y (z - y)‖ ≤ ε * ‖z - y‖ := by sorry

end GlobalInexactNewton.Backtracking
