-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_lemma_1_1
-- name    : GlobalInexactNewton.Backtracking.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:33:49.223003+00:00
-- url     : https://prove2.me/theorems/4b5eb558-9a30-4876-8613-97c2fa599869
-- title:
--   Lemma 1.1 — the inverse of $F'$ is continuous at a point where $F'$ is invertible
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Let $x\in E$ be a point at which the derivative $F'(x)$ is invertible. Then for every $\varepsilon>0$ there is $\delta>0$ such that, for every $y$ with $\|y-x\|<\delta$, $F'(y)$ is invertible and
--   $$\|F'(y)^{-1}-F'(x)^{-1}\|<\varepsilon,$$
--   where the norm on the left is the operator norm induced by the norm of $E$.
--
--   This is the analytic tool that keeps $\|F'(y)^{-1}\|$ uniformly bounded near a limit point at which $F'$ is invertible, in the proofs of Theorems 3.3 and 6.1.
--
--   **Formalization Note** $F'(y)^{-1}$ is `ContinuousLinearMap.inverse` of `fderiv ℝ F y`; invertibility is `ContinuousLinearMap.IsInvertible`. The neighbourhood $N_\delta(x)$ is the open ball. Continuous differentiability is the paper's standing assumption (p. 395).
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 395, Lemma 1.1

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 395, Lemma 1.1: if `F'(x)` is invertible, then for every `ε > 0`
there is `δ > 0` such that `F'(y)` is invertible and `‖F'(y)⁻¹ - F'(x)⁻¹‖ < ε` whenever
`y ∈ N_δ(x)`. Standing assumption (p. 395): `F` is continuously differentiable. -/
theorem lemma_1_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (hx : (fderiv ℝ F x).IsInvertible)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, (fderiv ℝ F y).IsInvertible ∧
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F x).inverse‖ < ε := by sorry

end GlobalInexactNewton.Backtracking
