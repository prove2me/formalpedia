-- Prove2me | Theorems.Thm_ImpulseGames_CostMonotonicity_xi_derivatives
-- name    : ImpulseGames.CostMonotonicity.xi_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:40:30.077628+00:00
-- url     : https://prove2.me/theorems/04f67c61-cd08-4d50-9114-2ea31ee47baf
-- title:
--   (4.28) — $\xi\in C^\infty(]0,\infty[)$, $\xi'=\frac\theta2\frac{\eta^2-\xi^2}{\xi^2}$, $\xi''=-\theta\eta^2\frac{\xi'}{\xi^3}=-\frac{\theta^2\eta^2}{2}\frac{\eta^2-\xi^2}{\xi^5}$
-- statement:
--   Under the standing assumptions of Section 4.1, let $\theta$, $\eta$ and $\xi(c)$ be as in (4.17), (4.21): for $c>0$, $\xi(c)$ is the unique zero in $(0,\eta)$ of $F_c(y) = 2y + \theta c - \eta\log\frac{\eta+y}{\eta-y}$. Then $c\mapsto\xi(c)$ is infinitely differentiable on $]0,\infty[$, and for every $c>0$
--   $$\xi'(c) = \frac{\theta}{2}\,\frac{\eta^2-\xi^2(c)}{\xi^2(c)}, \qquad \xi''(c) = -\theta\eta^2\,\frac{\xi'(c)}{\xi^3(c)} = -\frac{\theta^2\eta^2}{2}\,\frac{\eta^2-\xi^2(c)}{\xi^5(c)}.$$
--
--   In particular $\xi'>0$ and $\xi''<0$ on $]0,\infty[$. These signs drive the monotonicity of the thresholds in Propositions 4.13 and 4.14.
--
--   **Formalization Note.** $C^\infty$ is `ContDiffOn ℝ ∞` (smoothness of every finite order, not analyticity). $\xi'$ is Mathlib's `deriv ξ`; the second derivative is stated as `HasDerivAt (deriv ξ) … c`, which only depends on $\xi$ near $c>0$, where $\xi$ is the paper's function.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Section 4.4, (4.28) (p. 20)

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

open scoped ContDiff

namespace ImpulseGames.CostMonotonicity

theorem xi_derivatives (P : Params) (hP : P.Standing) :
    ContDiffOn ℝ ∞ P.xi (Set.Ioi 0) ∧
      ∀ c : ℝ, 0 < c →
        HasDerivAt P.xi (P.theta / 2 * ((P.eta ^ 2 - P.xi c ^ 2) / P.xi c ^ 2)) c ∧
        HasDerivAt (deriv P.xi) (-(P.theta * P.eta ^ 2) * (deriv P.xi c / P.xi c ^ 3)) c ∧
        -(P.theta * P.eta ^ 2) * (deriv P.xi c / P.xi c ^ 3) =
          -(P.theta ^ 2 * P.eta ^ 2 / 2) * ((P.eta ^ 2 - P.xi c ^ 2) / P.xi c ^ 5) := by sorry

end ImpulseGames.CostMonotonicity
