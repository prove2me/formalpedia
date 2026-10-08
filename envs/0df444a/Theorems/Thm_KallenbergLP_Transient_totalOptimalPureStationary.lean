-- Prove2me | Theorems.Thm_KallenbergLP_Transient_totalOptimalPureStationary
-- name    : KallenbergLP.Transient.totalOptimalPureStationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:40:36.444987+00:00
-- url     : https://prove2.me/theorems/fbd1b56f-99c2-48a1-8fff-f03e65bf5e96
-- title:
--   Theorem 3.2.1 — existence of a pure stationary total-optimal policy
-- statement:
--   Assume every policy has a possibly infinite expected total reward limit, as in Assumption 3.2.1. Define $v_i(R)$ as that limit for initial state $i$ and $v_i=\sup_{R\in C}v_i(R)$. Then one pure stationary policy $f^\infty$ is optimal simultaneously for all initial states:
--
--   $$v_i(f^\infty)=v_i\qquad(i\in E).$$
--
--   This supplies the stationary optimality result used in the chapter's transience arguments. The supremum defining $v_i$ includes every history-dependent randomized policy, and the values lie in $[-\infty,+\infty]$.
--
--   **Formalization Note** The extended-real limsup represents the total reward limit under the explicit convergence assumption.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 37, Assumption 3.2.1; p. 38, Theorem 3.2.1

import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.1: one pure stationary policy is total optimal for every initial state. -/
theorem totalOptimalPureStationary
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (h : TotalRewardExists M r) :
    ∃ f : PureRule M,
      ∀ i : Fin N, policyValue M r (purePolicy M f) i = valueVector M r i := by sorry

end KallenbergLP.Transient
