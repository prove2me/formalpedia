-- Prove2me | Theorems.Thm_MDPComplexity_Discounted_exists_stationary_optimal
-- name    : MDPComplexity.Discounted.exists_stationary_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:55.061748+00:00
-- url     : https://prove2.me/theorems/a7fc9d6a-c1f3-458d-a850-7ba239876219
-- title:
--   §2 (p. 444), §3 (p. 446) — a deterministic discounted process has a stationary optimal policy
-- statement:
--   Let $0<\beta<1$, and consider a finite deterministic stationary Markov decision process with initial state $s_0$. Then some **stationary** policy $\delta$ (one with $\delta(s,t)=\delta(s,0)$ for all $s,t$) is optimal among **all** policies $\delta'(s,t)$:
--
--   $$\sum_{t=0}^{\infty}\beta^t c\bigl(s_t,\delta(s_t,t)\bigr)\;\le\;\sum_{t=0}^{\infty}\beta^t c\bigl(s'_t,\delta'(s'_t,t)\bigr)\qquad\text{for every policy }\delta',$$
--
--   where $(s_t)$ and $(s'_t)$ are the state sequences generated from $s_0$ by $\delta$ and $\delta'$.
--
--   This is the deterministic special case of the classical fact the paper invokes ("It is well known that in the two latter cases ... there exist stationary optimal policies"); it is the step that reduces the optimization over infinite policies to a finite one over sigmas.
--
--   **Formalization Note** The paper cites this fact for general finite stochastic processes; its general form is on the platform as `BertsekasDP.discounted_main_theorem` (part 3). This item states the deterministic case directly in this mission's model, so that it can be used without translating between the two models. The comparison is between the discounted costs of every policy, with no reference to an infimum.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 444, §2 (existence of stationary optimal policies), and p. 446, §3, The infinite horizon, discounted case

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

namespace MDPComplexity.Discounted

theorem exists_stationary_optimal {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    ∃ δ : M.Policy, M.IsStationary δ ∧ ∀ δ' : M.Policy, M.discCost β s₀ δ ≤ M.discCost β s₀ δ' := by sorry

end MDPComplexity.Discounted
