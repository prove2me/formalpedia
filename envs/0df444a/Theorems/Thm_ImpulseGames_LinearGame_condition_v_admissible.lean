-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_condition_v_admissible
-- name    : ImpulseGames.LinearGame.condition_v_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:51:24.17179+00:00
-- url     : https://prove2.me/theorems/d82c1170-a778-4d73-bd96-19a648178c2a
-- title:
--   Condition (v) of the proof of Proposition 4.7: the equilibrium pair is $x$-admissible for every $x$
-- statement:
--   Assume the standing assumptions of Section 4.1 and $c>0$, let $W$ be a real Brownian motion on a probability space $(\Omega,\mathcal F,\mathbb P)$, let $\xi\in(0,\eta)$ be the zero of $F$ in (4.17), and fix $\tilde s\in\mathbb R$. Then for every initial state $x\in\mathbb R$ the pair
--   $$\varphi_1^*=(]\bar x_1,+\infty[,\delta_1),\qquad \varphi_2^*=(]-\infty,\bar x_2[,\delta_2)$$
--   is $x$-admissible: $(\varphi_1^*,\varphi_2^*)\in\Phi_x$ (Definition 2.5). In particular the discounted intervention costs are integrable,
--   $$\mathbb E_x\Big[\sum_{k\ge1}e^{-\rho\tau^*_{i,k}}\big(c+\lambda|\delta^*_{i,k}|\big)\Big]<\infty,\qquad i\in\{1,2\}.\tag{4.26}$$
--
--   Admissibility is the hypothesis of the verification theorem that makes the payoffs well defined and the Nash comparison meaningful.
--
--   **Formalization Note.** $\Phi_x$ is the structure `InPhi` of the game file. The hypothesis $c>0$ is added as in (4.17). $\delta_i$ replaces the paper's $\xi_i^*$ (see the equilibrium-strategies file).
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, proof of Proposition 4.7, Condition (v) and (4.26) (pp. 19-20)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ImpulseGames.LinearGame

/-- Condition (v) in the proof of Proposition 4.7 (pp. 19–20): for every initial state `x ∈ ℝ`,
the candidate equilibrium pair `((]x̄₁, ∞[, δ₁), (]−∞, x̄₂[, δ₂))` is `x`-admissible
(Definition 2.5). -/
theorem condition_v_admissible (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) (x : ℝ) :
    InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) := by sorry

end ImpulseGames.LinearGame
