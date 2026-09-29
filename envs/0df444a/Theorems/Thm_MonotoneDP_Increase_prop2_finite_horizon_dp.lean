-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop2_finite_horizon_dp
-- name    : MonotoneDP.Increase.prop2_finite_horizon_dp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:56:51.968259+00:00
-- url     : https://prove2.me/theorems/af66048d-0a59-447e-adfc-2e83b029b148
-- title:
--   Proposition 2 — J_N = T^N(J̄) under Assumptions I and I.2
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumption I (uniform increase) and Assumption I.2 for some scalar $\alpha>0$. For $N\ge1$ let
--
--   $$J_N(x)=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)(x)$$
--
--   be the optimal value of the $N$-stage problem. Then
--
--   $$J_N=T^N(\bar J)\qquad\text{for all }N=1,2,\dots$$
--
--   That is, the finite-horizon problem is solved by $N$ steps of the dynamic programming recursion, even though an infimum over policies is taken at each stage. The paper's Counterexample 1 (p. 448) shows the conclusion can fail when I.2 is dropped, even if I.1 holds.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 448 (PDF p. 11), Proposition 2 and eq. (36). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 448, Proposition 2: under Assumptions I and I.2, the optimal value
function of the `N`-stage problem (36) equals `T^N(J̄)` for all `N = 1, 2, …`. -/
theorem prop2_finite_horizon_dp {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ N : ℕ, 1 ≤ N → m.JN N = (m.T)^[N] m.Jbar := by sorry

end MonotoneDP.Increase
