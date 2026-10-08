-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_fixed_price
-- name    : MechanismDesign.DominantExamples.fixed_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:31:08.452234+00:00
-- url     : https://prove2.me/theorems/dd625725-33d7-49ba-80ee-9a80f2f9e159
-- title:
--   Proposition 4.12 — dominant strategy IC, ex post IR, exactly budget-balanced trading mechanisms are fixed-price mechanisms
-- statement:
--   Let $(q, t_S, t_B)$ be a deterministic direct bilateral trade mechanism on $\Theta = [\underline\theta_S,\bar\theta_S]\times[\underline\theta_B,\bar\theta_B]$, and suppose that the set $\{\theta \in \Theta \mid q(\theta) = 1\}$ is closed. Then the mechanism is dominant strategy incentive-compatible, ex post individually rational and ex post exactly budget balanced ($t_B = t_S$ on $\Theta$) if and only if either
--
--   1. $q(\theta) = 0$ and $t_S(\theta) = t_B(\theta) = 0$ for all $\theta \in \Theta$, or
--   2. there is a price $\hat\theta \in \mathbb R$ such that for all $\theta = (\theta_S,\theta_B) \in \Theta$:
--   $$\begin{aligned} q(\theta) = 1 \text{ and } t_S(\theta) = t_B(\theta) = \hat\theta &\quad\text{if } \theta_S \le \hat\theta \text{ and } \theta_B \ge \hat\theta,\\ q(\theta) = 0 \text{ and } t_S(\theta) = t_B(\theta) = 0 &\quad\text{if } \theta_S > \hat\theta \text{ or } \theta_B < \hat\theta.\end{aligned}$$
--
--   These are fixed-price mechanisms: trade happens at a price that does not depend on the reports, exactly when the buyer's value is at least the price and the seller's value is at most the price.
--
--   **Formalization Note** Closedness is required of the set of type vectors in $\Theta$ at which trade takes place, as a subset of $\mathbb R^2$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.93, Proposition 4.12

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.12, p.93. Suppose that the set `{θ ∈ Θ | q(θ) = 1}` is closed. A direct
bilateral trade mechanism is dominant strategy incentive-compatible, ex post individually
rational and ex post exactly budget balanced if and only if either
`q(θ) = 0` and `t_S(θ) = t_B(θ) = 0` for all `θ ∈ Θ`,
or there is a price `θ̂ ∈ ℝ` such that for all `θ = (θ_S, θ_B) ∈ Θ`:
`q(θ) = 1` and `t_S(θ) = t_B(θ) = θ̂` if `θ_S ≤ θ̂` and `θ_B ≥ θ̂`;
`q(θ) = 0` and `t_S(θ) = t_B(θ) = 0` if `θ_S > θ̂` or `θ_B < θ̂`. -/
theorem fixed_price {E : TradeSetting} (M : TradeMechanism E)
    (hclosed : IsClosed {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsExactlyBudgetBalanced) ↔
      ((∀ θ ∈ E.typeSpace, M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0) ∨
        ∃ θhat : ℝ, ∀ θ ∈ E.typeSpace,
          ((θ.1 ≤ θhat ∧ θhat ≤ θ.2) → M.q θ = 1 ∧ M.tS θ = θhat ∧ M.tB θ = θhat) ∧
          ((θhat < θ.1 ∨ θ.2 < θhat) → M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0)) := by sorry

end MechanismDesign.DominantExamples
