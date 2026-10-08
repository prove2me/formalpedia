-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_two_agent_fixed_cost_shares
-- name    : MechanismDesign.DominantExamples.two_agent_fixed_cost_shares
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:28.979765+00:00
-- url     : https://prove2.me/theorems/1fd11abd-1dff-49c3-95a6-222b336ae11c
-- title:
--   Proposition 4.8 — with two agents, dominant strategy IC, ex post IR, budget-balanced public good mechanisms are fixed cost shares
-- statement:
--   Consider the public goods problem with two agents, $N = 2$, cost $c > 0$ and types in $[\underline\theta,\bar\theta]$, $0 \le \underline\theta < \bar\theta$. Let $(q, t_1, t_2)$ be a deterministic direct mechanism, and suppose that the set $\{\theta \in \Theta \mid q(\theta) = 1\}$ is closed. Then the mechanism is dominant strategy incentive-compatible, ex post individually rational and ex post budget balanced ($t_1(\theta) + t_2(\theta) = c\,q(\theta)$ for every $\theta$) if and only if there are payments $\tau_1, \tau_2 \in \mathbb R$ with
--   $$\tau_1 + \tau_2 = c$$
--   such that for all $\theta = (\theta_1,\theta_2) \in \Theta$:
--   $$\begin{aligned} q(\theta) = 1 \text{ and } t_i(\theta) = \tau_i \text{ for both } i &\quad\text{if } \theta_1 \ge \tau_1 \text{ and } \theta_2 \ge \tau_2,\\ q(\theta) = 0 \text{ and } t_i(\theta) = 0 \text{ for both } i &\quad\text{otherwise.}\end{aligned}$$
--
--   In words: each agent is assigned a fixed share $\tau_i$ of the cost, the good is produced exactly when both agents are willing to pay their share, and payments do not depend on the reported valuations beyond that. Dominant strategy incentive compatibility together with exact budget balance thus leaves no room for mechanisms that adapt the cost shares to the agents' valuations. The shares need not be nonnegative, and the statement fails for three or more agents (the book's example on p.90).
--
--   **Formalization Note** The agents are `Fin 2`; indices `0, 1` stand for the book's `1, 2`. Budget balance is the equality of §4.3.2, not the inequality of Definition 3.5. Closedness is required of the set of type vectors in $\Theta$ at which the good is produced, as a subset of $\mathbb R^2$ (equivalently of $\Theta$, which is closed).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.88, Proposition 4.8

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.8, p.88. Suppose `N = 2` (agents `0, 1` stand for the book's `1, 2`) and that
the set `{θ ∈ Θ | q(θ) = 1}` is closed. Then a direct public good mechanism is dominant
strategy incentive-compatible, ex post individually rational and ex post (exactly) budget
balanced if and only if there are payments `τ_1, τ_2 ∈ ℝ` with `τ_1 + τ_2 = c` such that for
all `θ ∈ Θ`:
`q(θ) = 1` and `t_i(θ) = τ_i` for both `i` if `θ_1 ≥ τ_1` and `θ_2 ≥ τ_2`;
`q(θ) = 0` and `t_i(θ) = 0` for both `i` otherwise. -/
theorem two_agent_fixed_cost_shares {E : PublicGoodSetting} (M : PublicGoodMechanism E (Fin 2))
    (hclosed : IsClosed {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsBudgetBalanced) ↔
      ∃ τ : Fin 2 → ℝ, τ 0 + τ 1 = E.c ∧ ∀ θ ∈ E.typeSpace (Fin 2),
        ((τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 1 ∧ ∀ i, M.t i θ = τ i) ∧
        (¬ (τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 0 ∧ ∀ i, M.t i θ = 0) := by sorry

end MechanismDesign.DominantExamples
