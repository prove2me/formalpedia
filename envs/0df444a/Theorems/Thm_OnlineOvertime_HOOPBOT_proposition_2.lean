-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_proposition_2
-- name    : OnlineOvertime.HOOPBOT.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:45.652378+00:00
-- url     : https://prove2.me/theorems/0bd00cfb-eb9a-4a2f-8325-e113d1ff3ce3
-- title:
--   Proposition 2, p. 19 — the dual solution (x, u, z) built by HOOP-BOT is feasible for (D)
-- statement:
--   Let an instance of online scheduling with budgeted overtime satisfy the standing assumptions, let $\theta_1,\theta_2\ge 0$, and run Algorithm 1 (HOOP-BOT) with coefficients $\theta_1,\theta_2$ and any tie-break for the argmax of Step 3. Let $(x,u,z)$ be the dual prices after the first $k$ customers have been processed. Then
--
--   1. $b_{i,j}x_{i,t}+z_j\ge c_{i,j}$ for every server-date $(i,t)$ and every processed customer $j$ (constraint (8));
--   2. $x_{i,t}-u_{i,t}\le d_i$ for every $(i,t)$ (constraint (9));
--   3. $x_{i,t}\ge 0$, $u_{i,t}\ge 0$ and $z_j\ge 0$ (constraint (10)).
--
--   In particular, after all $m$ customers,
--   $$(x,u,z)\ \text{is feasible for the dual problem (D)}.$$
--
--   This is the dual half of the primal-dual analysis: the final prices give an upper bound on the offline optimum by weak duality.
--
--   **Formalization Note** The page states the result "at each iteration $j$"; the Lean statement is posed for the state after every prefix of $k$ customers, with constraint (8) for the customers processed so far (for unprocessed customers $z_j=0$ and (8) need not hold). The coefficients are assumed nonnegative, as they are throughout §4.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 19, Proposition 2

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Proposition 2 (Dual Feasibility Guarantee), p. 19. For nonnegative coefficients
`θ1, θ2` and every argmax tie-break, after the first `k` customers have been processed by
Algorithm 1 the prices `(x, u, z)` satisfy the dual constraint (8) for every processed
customer and the dual constraints (9)–(10). For `k = m` this is `DualFeasible`. -/
theorem proposition_2 {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (θ1 θ2 : ℝ) (hθ1 : 0 ≤ θ1) (hθ2 : 0 ≤ θ2)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (hsel : IsArgmaxSelector sel) (k : ℕ) :
    let s := runPrefix I θ1 θ2 sel k
    (∀ (i : Fin n) (t : Fin T) (j : Fin m), j.val < k → I.c j i ≤ I.b j i * s.x i t + s.z j) ∧
    (∀ i t, s.x i t - s.u i t ≤ I.d i) ∧
    (∀ i t, 0 ≤ s.x i t) ∧ (∀ i t, 0 ≤ s.u i t) ∧ (∀ j, 0 ≤ s.z j) := by sorry

end OnlineOvertime.HOOPBOT
