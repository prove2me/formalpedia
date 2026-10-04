-- Prove2me | Theorems.Thm_ImpulseGames_CostMonotonicity_xbar_monotone
-- name    : ImpulseGames.CostMonotonicity.xbar_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:40:27.646985+00:00
-- url     : https://prove2.me/theorems/e5ad0717-f336-4bdd-a15f-e4dea24b6c17
-- title:
--   Proposition 4.13 — on $]\tilde c,+\infty[$, $c\mapsto\bar x_2(c)$ is increasing and $c\mapsto\bar x_1(c)$ is decreasing
-- statement:
--   Consider the linear two-player impulse game of Section 4.1 with discount rate $\rho$, volatility $\sigma$, fixed and proportional intervention costs $c$, $\lambda$, fixed and proportional gains $\tilde c$, $\tilde\lambda$, and running-payoff targets $s_1<s_2$, under the standing assumptions
--   $$\rho>0,\quad\sigma>0,\quad\tilde c\ge0,\quad\lambda\ge\tilde\lambda\ge0,\quad1-\lambda\rho>0.$$
--   Let $\theta=\sqrt{2\rho/\sigma^2}$, $\eta=(1-\lambda\rho)/\rho$, let $\xi(c)\in(0,\eta)$ be the unique zero of $F_c(y)=2y+\theta c-\eta\log\frac{\eta+y}{\eta-y}$, let $\Gamma(c)=\frac{\theta(c-\tilde c)}{4\xi}+\frac{\theta c(\lambda-\tilde\lambda)}{4\eta\xi}+\frac{\lambda-\tilde\lambda}{2\eta}$, fix $\tilde s\in\mathbb R$, and let
--   $$\bar x_i(c) = \tilde s + \frac{(-1)^i}{\theta}\log\left[\sqrt{\frac{\eta+\xi(c)}{\eta-\xi(c)}}\left(\sqrt{\Gamma(c)+1}+\sqrt{\Gamma(c)}\right)\right],\qquad i\in\{1,2\},$$
--   be the thresholds (4.20) of the Nash equilibrium of Proposition 4.7. Then
--   $$c\mapsto\bar x_2(c)\ \text{is strictly increasing and}\ c\mapsto\bar x_1(c)\ \text{is strictly decreasing on}\ ]\tilde c,+\infty[.$$
--
--   Player 1 intervenes below $\bar x_1$ and player 2 above $\bar x_2$, so the common continuation region $]\bar x_1(c),\bar x_2(c)[$ grows strictly as the fixed cost of intervening increases: the players intervene less when intervening costs more.
--
--   **Formalization Note.** The statement is about the explicit functions (4.20)–(4.21); the equilibrium property of Proposition 4.7 is not part of it. "Increasing" is read strictly, as the paper's proof gives. The domain is $]\tilde c,+\infty[$ for both claims, where $\Gamma(c)>0$ and $\xi(c)$ is the paper's zero; outside it the Lean functions take placeholder values that the statement does not see.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.13 (p. 22)

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

namespace ImpulseGames.CostMonotonicity

theorem xbar_monotone (P : Params) (hP : P.Standing) :
    StrictMonoOn P.xbar2 (Set.Ioi P.cTilde) ∧ StrictAntiOn P.xbar1 (Set.Ioi P.cTilde) := by sorry

end ImpulseGames.CostMonotonicity
