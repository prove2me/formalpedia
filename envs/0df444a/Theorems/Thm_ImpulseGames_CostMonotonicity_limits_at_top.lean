-- Prove2me | Theorems.Thm_ImpulseGames_CostMonotonicity_limits_at_top
-- name    : ImpulseGames.CostMonotonicity.limits_at_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:39:51.867989+00:00
-- url     : https://prove2.me/theorems/c263efea-852d-4346-92a8-407f3c0d99d8
-- title:
--   Proposition 4.12 — as $c\to+\infty$: $\bar x_2, x_1^*\to+\infty$, $\bar x_1, x_2^*\to-\infty$, $V_1^c\to\frac{x-s_1}{\rho}$, $V_2^c\to\frac{s_2-x}{\rho}$
-- statement:
--   Under the standing assumptions of Section 4.1 ($\rho>0$, $\sigma>0$, $s_1<s_2$, $\tilde c\ge0$, $\lambda\ge\tilde\lambda\ge0$, $1-\lambda\rho>0$), let $\bar x_i(c)$, $x_i^*(c)$ be the thresholds and targets (4.20) and $V_i^c$ the equilibrium payoffs (4.27) of the linear impulse game with fixed intervention cost $c$. Then, as $c\to+\infty$,
--   $$\bar x_2(c)\to+\infty,\quad x_1^*(c)\to+\infty,\quad \bar x_1(c)\to-\infty,\quad x_2^*(c)\to-\infty,$$
--   and for every $x\in\mathbb R$
--   $$V_1^c(x)\to\frac{x-s_1}{\rho}, \qquad V_2^c(x)\to\frac{s_2-x}{\rho}.$$
--
--   When intervening becomes prohibitively expensive, the continuation region $]\bar x_1(c),\bar x_2(c)[$ invades the whole line and each player's payoff converges to the payoff of never intervening on an uncontrolled Brownian motion.
--
--   **Formalization Note.** The payoff limits are pointwise in $x$. The formulas (4.20), (4.27) are the explicit ones of the paper, with $\xi(c)$ the zero of (4.17); no equilibrium property is assumed or used in the statement.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.12 (p. 22)

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

open Filter Topology

namespace ImpulseGames.CostMonotonicity

theorem limits_at_top (P : Params) (hP : P.Standing) :
    Tendsto P.xbar2 atTop atTop ∧ Tendsto P.xstar1 atTop atTop ∧
      Tendsto P.xbar1 atTop atBot ∧ Tendsto P.xstar2 atTop atBot ∧
      (∀ x : ℝ, Tendsto (fun c => P.V1 c x) atTop (𝓝 ((x - P.s1) / P.rho))) ∧
      (∀ x : ℝ, Tendsto (fun c => P.V2 c x) atTop (𝓝 ((P.s2 - x) / P.rho))) := by sorry

end ImpulseGames.CostMonotonicity
