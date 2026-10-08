-- Prove2me | Theorems.Thm_KallenbergLP_Positive_extreme_optimal_dual_yields_policy
-- name    : KallenbergLP.Positive.extreme_optimal_dual_yields_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:17:42.158985+00:00
-- url     : https://prove2.me/theorems/e36d98f3-d959-445a-b5c3-d4049fc3a31b
-- title:
--   Theorem 3.5.2 — an extreme optimal dual solution yields a pure stationary optimal policy
-- statement:
--   Consider the positive dynamic programming model: $r_{ia}\ge0$ for every admissible state-action pair, and the dual program (3.5.2) with given weights $\beta_j>0$. Suppose $x^*$ is an **extreme optimal solution** of its feasible region, with the optimality comparison taken over every feasible flow. Set
--   $$
--   E_{x^*}=\left\{i\in E:\sum_{a\in A(i)}x^*_{ia}>0\right\}.
--   $$
--   For **every** pure stationary rule $f$ that chooses an action with $x^*_{i,f(i)}>0$ at each $i\in E_{x^*}$ and any admissible action elsewhere, the policy $f^\infty$ is total optimal:
--   $$
--   v_i(f^\infty)=v_i=\sup_{R\in C}v_i(R)\qquad\text{for every }i\in E.
--   $$
--
--   This extracts a policy optimal from every initial state from one extreme optimal dual solution. The comparison class $C$ includes randomized, history dependent and nontransient policies.
--
--   **Formalization Note** The dual inequalities have the book's $\le\beta_j$ orientation. Extreme means an extreme point in the flow-only feasible region. The existence of $x^*$ itself implies the finite optimum case; no finiteness of all policies is separately assumed.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 78–80 (PDF pp. 86–88), equation (3.5.2) and Theorem 3.5.2

import Definitions.Def_KallenbergLP_Positive_Dual

namespace KallenbergLP.Positive

/-- Theorem 3.5.2. Every admissible pure rule that selects a positive-flow
action on `E_x` is optimal among all policies, including nontransient ones. -/
theorem extreme_optimal_dual_yields_policy
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (hβ : ∀ j, 0 < β j)
    (x : Flow M)
    (hx : IsDualOptimal M β x)
    (hext : x ∈ Set.extremePoints ℝ (dualFeasible M β)) :
    ∀ f : PureRule M,
      (∀ i, i ∈ occupiedStates M x →
        0 < x i ⟨f.choose i, f.admissible i⟩) →
      ∀ i : Fin N, totalReward M (purePolicy M f) i = value M i := by sorry

end KallenbergLP.Positive
