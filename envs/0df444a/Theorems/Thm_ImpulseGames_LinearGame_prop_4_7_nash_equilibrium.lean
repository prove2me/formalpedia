-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_prop_4_7_nash_equilibrium
-- name    : ImpulseGames.LinearGame.prop_4_7_nash_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:51:48.61365+00:00
-- url     : https://prove2.me/theorems/2b17c77f-4ddb-4a6a-a941-c0610bb27573
-- title:
--   Proposition 4.7: threshold strategies give a Nash equilibrium of the linear impulse game, with payoffs $\tilde V_1,\tilde V_2$
-- statement:
--   Consider the linear impulse game of Section 4.1: the state is $X_s=x+\sigma W_s+\sum_{k:\tau_{1,k}\le s}\delta_{1,k}+\sum_{k:\tau_{2,k}\le s}\delta_{2,k}$ for a real Brownian motion $W$; player 1 (impulses $\delta\ge0$) receives the running payoff $X_s-s_1$, player 2 (impulses $\delta\le0$) receives $s_2-X_s$; an impulse $\delta$ costs its author $c+\lambda|\delta|$ and pays the opponent $\tilde c+\tilde\lambda|\delta|$; everything is discounted at rate $\rho$. Assume the standing assumptions
--   $$\sigma>0,\ \rho>0,\ s_1<s_2,\ c\ge\tilde c\ge0,\ \lambda\ge\tilde\lambda\ge0,\ (c,\lambda)\ne(\tilde c,\tilde\lambda),\ 1-\lambda\rho>0,$$
--   and $c>0$. Let $\xi\in(0,\eta)$ be the zero of $F$ in (4.17), and for $\tilde s\in\mathbb R$ let $\bar x_i,x_i^*$ be given by (4.20) and $\tilde V_1,\tilde V_2$ by Definition 4.1.
--
--   Then for every $\tilde s\in\mathbb R$ and every initial state $x\in\mathbb R$, the strategies
--   $$\varphi_1^*=\big(]\bar x_1,+\infty[,\ \delta_1\big),\qquad \varphi_2^*=\big(]-\infty,\bar x_2[,\ \delta_2\big),\qquad \delta_1(y)=\max(x_1^*-y,0),\ \delta_2(y)=\min(x_2^*-y,0),$$
--   form an $x$-admissible pair which is a Nash equilibrium (Definition 2.6), and the equilibrium payoffs are
--   $$J^1(x;\varphi_1^*,\varphi_2^*)=\tilde V_1(x),\qquad J^2(x;\varphi_1^*,\varphi_2^*)=\tilde V_2(x).$$
--
--   The result exhibits infinitely many Nash equilibria, indexed by $\tilde s$, with explicit threshold strategies and explicit payoff functions, for a nonzero-sum stochastic differential game with impulse controls.
--
--   **Formalization Note.** Deviations range over all strategies of Definition 2.1 (open continuation region, continuous impulse map) that keep the pair in $\Phi_x$. The paper's $\xi_i^*(y)=x_i^*-y$ is replaced by $\delta_i$ of (4.23), which coincides with it wherever player $i$ acts and is $Z_i$-valued. The hypothesis $c>0$ is added: with $c=0$ the zero $\xi$ and the 8-uple (4.20) do not exist. The Brownian motion is Mathlib's `IsBrownianReal` (almost surely continuous paths); all constructions are pathwise.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.7 (p. 18)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ImpulseGames.LinearGame

/-- Proposition 4.7 (p. 18): for every `s̃ ∈ ℝ` and every initial state `x ∈ ℝ`, the pair
`φ₁* = (]x̄₁, +∞[, δ₁)`, `φ₂* = (]−∞, x̄₂[, δ₂)` is an `x`-admissible Nash equilibrium of the
linear impulse game of Section 4.1, and its payoffs are `J¹(x; φ₁*, φ₂*) = Ṽ₁(x)`,
`J²(x; φ₁*, φ₂*) = Ṽ₂(x)`. -/
theorem prop_4_7_nash_equilibrium (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) (x : ℝ) :
    InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) ∧
    IsNash M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) ∧
    J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .one = Vt1 M ξ s x ∧
    J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .two = Vt2 M ξ s x := by sorry

end ImpulseGames.LinearGame
