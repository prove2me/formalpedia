-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_prop8_optimal_stationary_criterion
-- name    : MonotoneDP.Decrease.prop8_optimal_stationary_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:05:23.578592+00:00
-- url     : https://prove2.me/theorems/e3ad0729-5d32-4512-b870-9cc27f76e75e
-- title:
--   Proposition 8 — a stationary policy is optimal iff T_{μ*}(J_{μ*}) = T(J_{μ*}), under D and D.1
-- statement:
--   In the abstract dynamic programming model of Bertsekas (1977), suppose Assumptions D and D.1 hold. Then a stationary policy $\pi^*=\{\mu^*,\mu^*,\dots\}$ is optimal, i.e. $J_{\mu^*}=J^*$, if and only if
--
--   $$T_{\mu^*}(J_{\mu^*})=T(J_{\mu^*}).\tag{48}$$
--
--   Under uniform decrease, a stationary policy is therefore optimal exactly when it attains the minimum in Bellman's equation at its own cost function $J_{\mu^*}$ (not at $J^*$, as under Assumption I).
--
--   **Formalization Note** "Optimal" is stated as the equality of functions $J_{\mu^*}=J^*$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 455 (PDF p. 18), Proposition 8, eq. (48). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 455, Proposition 8: under D and D.1, a stationary policy
`{μ*, μ*, …}` is optimal (`J_{μ*} = J*`) if and only if (48) `T_{μ*}(J_{μ*}) = T(J_{μ*})`. -/
theorem prop8_optimal_stationary_criterion {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Jstar ↔ m.Tmu μ (m.Jmu μ) = m.T (m.Jmu μ) := by sorry

end MonotoneDP.Decrease
