-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_prop3_finite_horizon_dp
-- name    : MonotoneDP.Decrease.prop3_finite_horizon_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:03:40.162948+00:00
-- url     : https://prove2.me/theorems/d521f7bd-87da-4151-a27e-4e674ae58282
-- title:
--   Proposition 3 — J_N = T^N(J̄) under D and either D.1, or D.2 with T^N(J̄) > −∞
-- statement:
--   In the abstract dynamic programming model of Bertsekas (1977), let $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$ and let $J_N(x)=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)(x)$ be the optimal value function of the $N$-stage problem, for a positive integer $N$. Suppose Assumption D holds, and that either
--
--   1. Assumption D.1 holds, or
--   2. Assumption D.2 holds and $T^N(\bar J)(x)>-\infty$ for all $x\in S$.
--
--   Then
--
--   $$J_N=T^N(\bar J).$$
--
--   That is, the dynamic programming algorithm $\bar J, T(\bar J), T^2(\bar J),\dots$ computes the finite-horizon optimal values. The paper's Counterexamples 2 and 3 show that the conclusion can fail when D.1 is dropped and either D.2 or the condition $T^N(\bar J)>-\infty$ is dropped.
--
--   **Formalization Note** $N$ is a fixed natural number with $N\ge1$, and the condition $T^N(\bar J)(x)>-\infty$ (written $\ne\bot$) belongs to the D.2 branch only, for the same $N$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 448 (PDF p. 11), Proposition 3. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 448, Proposition 3: let D hold, fix a positive integer `N`, and assume
that either D.1 holds, or D.2 holds and `T^N(J̄)(x) > −∞` for all `x ∈ S`. Then `J_N = T^N(J̄)`. -/
theorem prop3_finite_horizon_dp {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (N : ℕ) (hN : 1 ≤ N)
    (h : m.AssumptionD1 ∨
      ((∃ α : ℝ, m.AssumptionD2 α) ∧ ∀ x, (m.T)^[N] m.Jbar x ≠ ⊥)) :
    m.JN N = (m.T)^[N] m.Jbar := by sorry

end MonotoneDP.Decrease
