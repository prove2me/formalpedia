-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_prop_4_7_player_one_optimal
-- name    : ImpulseGames.LinearGame.prop_4_7_player_one_optimal
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:16:57.698565+00:00
-- url     : https://prove2.me/theorems/9c4803d5-9f20-416d-964b-64d3bc6c4fc8
-- title:
--   Proposition 4.7, player 1: no profitable deviation from the threshold strategy, and $J^1=\tilde V_1$
-- statement:
--   In the linear impulse game of Section 4.1 under the standing assumptions, fix $\tilde s\in\mathbb R$ and $\xi$, and suppose the thresholds of (4.20) satisfy the order conditions (4.7) and the pasting conditions (4.8a)–(4.8d) for $\varphi_1$:
--   $$\bar x_1<x_1^*<\bar x_2,\quad \bar x_1<x_2^*<\bar x_2,\quad \varphi_1'(x_1^*)=\varphi_1'(\bar x_1)=\lambda,$$
--   $$\varphi_1(\bar x_1)=\varphi_1(x_1^*)-c-\lambda(x_1^*-\bar x_1),\qquad \varphi_1(\bar x_2)=\varphi_1(x_2^*)+\tilde c+\tilde\lambda(\bar x_2-x_2^*),$$
--   and that $\tilde V_1\ge\mathcal M_1\tilde V_1$, i.e. $\tilde V_1(y+\delta)-c-\lambda|\delta|\le\tilde V_1(y)$ for all $y\in\mathbb R$, $\delta\ge0$. Then for every initial state $x$: every strategy $\psi_1$ of player 1 with $(\psi_1,\varphi_2^*)$ $x$-admissible satisfies $J^1(x;\psi_1,\varphi_2^*)\le\tilde V_1(x)$, and if $(\varphi_1^*,\varphi_2^*)$ is $x$-admissible then $J^1(x;\varphi_1^*,\varphi_2^*)=\tilde V_1(x)$.
--
--   Role: this is the verification step (Theorem 3.3, conditions (i)–(iv)) for player 1 in the proof of Proposition 4.7: it yields both player 1's equilibrium inequality and the identity $J^1=\tilde V_1$.
--
--   **Formalization Note**: $\tilde V_1\ge\mathcal M_1\tilde V_1$ is stated pointwise in $\delta$ (equivalent to the supremum form of (4.24)); the Brownian motion is evaluated pathwise as in the parent.
-- source:
--   Aïd, Basei, Callegaro, Campi, Vargiolu, Nonzero-sum stochastic differential games with impulse controls: a verification theorem with applications, Math. Oper. Res. 45(1) (2020), arXiv:1605.00039, proof of Proposition 4.7 (pp. 18-20), conditions (i)-(iv) of Theorem 3.3 for player 1

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ImpulseGames.LinearGame

theorem prop_4_7_player_one_optimal (M : Model) (hM : M.Standing) (ξ s : ℝ)
    (h47a : xbar M ξ s 1 < xstar M ξ s 1 ∧ xstar M ξ s 1 < xbar M ξ s 2)
    (h47b : xbar M ξ s 1 < xstar M ξ s 2 ∧ xstar M ξ s 2 < xbar M ξ s 2)
    (h48a : deriv (phiOne M ξ s) (xstar M ξ s 1) = M.lam)
    (h48b : deriv (phiOne M ξ s) (xbar M ξ s 1) = M.lam)
    (h48c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h48d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2))
    (hQVI : ∀ y δ : ℝ, 0 ≤ δ → Vt1 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt1 M ξ s y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (x : ℝ) :
    (∀ ψ₁ : Strategy Z₁, InPhi M P W x ψ₁ (eqStrat2 M ξ s) →
      J M P W x ψ₁ (eqStrat2 M ξ s) .one ≤ Vt1 M ξ s x) ∧
    (InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) →
      J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .one = Vt1 M ξ s x) := by sorry

end ImpulseGames.LinearGame
