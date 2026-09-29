-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_prop9_dp_convergence
-- name    : MonotoneDP.Decrease.prop9_dp_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:05:54.978514+00:00
-- url     : https://prove2.me/theorems/24a88cac-5902-47a6-bccc-5462d0e5a812
-- title:
--   Proposition 9 — under D, and D.1 or J_N = T^N(J̄) for all N, the DP algorithm converges: J_∞ = J*
-- statement:
--   In the abstract dynamic programming model of Bertsekas (1977), the dynamic programming algorithm generates $T(\bar J),T^2(\bar J),\dots$, where $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$, and its limit is
--
--   $$J_\infty(x)=\lim_{N\to\infty}T^N(\bar J)(x)\qquad(x\in S).\tag{49}$$
--
--   Let $J_N$ be the optimal value function of the $N$-stage problem (36) and $J^*=\inf_{\pi\in\Pi}J_\pi$ the optimal value function. Suppose Assumption D holds, and that either
--
--   1. Assumption D.1 holds, or
--   2. $J_N=T^N(\bar J)$ for all $N=1,2,\dots$.
--
--   Then
--
--   $$J_\infty=J^*.$$
--
--   That is, under uniform decrease the value iteration started from $\bar J$ converges to the optimal value function. Under the uniform increase assumption the analogous statement can fail even for simple deterministic problems.
--
--   **Formalization Note** $J_\infty$ is `limUnder atTop` of the sequence $T^N(\bar J)(x)$, which is nonincreasing under D and so converges in $[-\infty,\infty]$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 456 (PDF p. 19), Proposition 9; eq. (49) on pp. 455–456. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 456, Proposition 9: let D hold and assume that either D.1 holds or else
`J_N = T^N(J̄)` for all `N = 1, 2, …`, where `J_N` is the optimal value function of the `N`-stage
problem (36). Then `J_∞ = J*`, where `J_∞(x) = lim_N T^N(J̄)(x)` (49). -/
theorem prop9_dp_convergence {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (h : m.AssumptionD1 ∨ ∀ N : ℕ, 1 ≤ N → m.JN N = (m.T)^[N] m.Jbar) :
    m.Jinf = m.Jstar := by sorry

end MonotoneDP.Decrease
