-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_prop_4_7_player_two_optimal
-- name    : ImpulseGames.LinearGame.prop_4_7_player_two_optimal
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:17:37.686193+00:00
-- url     : https://prove2.me/theorems/bde572cd-fc60-421d-87d0-b03f1bf5ffd0
-- title:
--   Proposition 4.7, player 2: no profitable deviation from the threshold strategy, and $J^2=\tilde V_2$
-- statement:
--   In the linear impulse game of Section 4.1 under the standing assumptions, fix $\tilde s\in\mathbb R$ and $\xi$, and suppose the thresholds of (4.20) satisfy the order conditions (4.7) and the pasting conditions (4.9a)–(4.9d) for $\varphi_2$:
--   $$\bar x_1<x_1^*<\bar x_2,\quad \bar x_1<x_2^*<\bar x_2,\quad \varphi_2'(x_2^*)=\varphi_2'(\bar x_2)=-\lambda,$$
--   $$\varphi_2(\bar x_1)=\varphi_2(x_1^*)+\tilde c+\tilde\lambda(x_1^*-\bar x_1),\qquad \varphi_2(\bar x_2)=\varphi_2(x_2^*)-c-\lambda(\bar x_2-x_2^*),$$
--   and that $\tilde V_2\ge\mathcal M_2\tilde V_2$, i.e. $\tilde V_2(y+\delta)-c-\lambda|\delta|\le\tilde V_2(y)$ for all $y\in\mathbb R$, $\delta\le0$. Then for every initial state $x$: every strategy $\psi_2$ of player 2 with $(\varphi_1^*,\psi_2)$ $x$-admissible satisfies $J^2(x;\varphi_1^*,\psi_2)\le\tilde V_2(x)$, and if $(\varphi_1^*,\varphi_2^*)$ is $x$-admissible then $J^2(x;\varphi_1^*,\varphi_2^*)=\tilde V_2(x)$.
--
--   Role: this is the verification step (Theorem 3.3, conditions (i)–(iv)) for player 2 in the proof of Proposition 4.7: it yields both player 2's equilibrium inequality and the identity $J^2=\tilde V_2$.
--
--   **Formalization Note**: $\tilde V_2\ge\mathcal M_2\tilde V_2$ is stated pointwise in $\delta$ (equivalent to the supremum form of (4.24)); the Brownian motion is evaluated pathwise as in the parent.
-- source:
--   Aïd, Basei, Callegaro, Campi, Vargiolu, Nonzero-sum stochastic differential games with impulse controls: a verification theorem with applications, Math. Oper. Res. 45(1) (2020), arXiv:1605.00039, proof of Proposition 4.7 (pp. 18-20), conditions (i)-(iv) of Theorem 3.3 for player 2

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ImpulseGames.LinearGame

theorem prop_4_7_player_two_optimal (M : Model) (hM : M.Standing) (ξ s : ℝ)
    (h47a : xbar M ξ s 1 < xstar M ξ s 1 ∧ xstar M ξ s 1 < xbar M ξ s 2)
    (h47b : xbar M ξ s 1 < xstar M ξ s 2 ∧ xstar M ξ s 2 < xbar M ξ s 2)
    (h49a : deriv (phiTwo M ξ s) (xstar M ξ s 2) = -M.lam)
    (h49b : deriv (phiTwo M ξ s) (xbar M ξ s 2) = -M.lam)
    (h49c : phiTwo M ξ s (xbar M ξ s 1) =
      phiTwo M ξ s (xstar M ξ s 1) + M.ct + M.lamt * (xstar M ξ s 1 - xbar M ξ s 1))
    (h49d : phiTwo M ξ s (xbar M ξ s 2) =
      phiTwo M ξ s (xstar M ξ s 2) - M.c - M.lam * (xbar M ξ s 2 - xstar M ξ s 2))
    (hQVI : ∀ y δ : ℝ, δ ≤ 0 → Vt2 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt2 M ξ s y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (x : ℝ) :
    (∀ ψ₂ : Strategy Z₂, InPhi M P W x (eqStrat1 M ξ s) ψ₂ →
      J M P W x (eqStrat1 M ξ s) ψ₂ .two ≤ Vt2 M ξ s x) ∧
    (InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) →
      J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .two = Vt2 M ξ s x) := by sorry

end ImpulseGames.LinearGame
