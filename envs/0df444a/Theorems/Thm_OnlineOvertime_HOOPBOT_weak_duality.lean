-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_weak_duality
-- name    : OnlineOvertime.HOOPBOT.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:45.563078+00:00
-- url     : https://prove2.me/theorems/c17f8d1c-3ec4-41c0-8503-71af4a34cfc7
-- title:
--   Proof of Proposition 4, (25), p. 24 — weak duality f∗ ≤ g_D between (P) and (D)
-- statement:
--   Let an instance satisfy the standing assumptions. If $(y,v)$ is feasible for the offline integer program (P) and $(x,u,z)$ is feasible for the dual (D), then
--   $$\sum_{t}\sum_{i}\sum_{j}c_{i,j}y_{i,j,t}-\sum_t\sum_i d_iv_{i,t}\ \le\ \sum_t\sum_i\big(B_{i,t}x_{i,t}+U_{i,t}u_{i,t}\big)+\sum_j z_j.$$
--
--   Applied to an optimal offline solution and to the dual produced by Algorithm 1, this is the inequality $f^*\le g_D$ used in (25) to bound the competitive ratio.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 24, proof of Proposition 4, (25): 'By weak duality, we have f∗ ≤ gD'

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Weak duality, proof of Proposition 4, (25), p. 24: the objective (2) of every feasible point
of (P) is at most the objective (7) of every feasible point of (D), so `f∗ ≤ g_D`. -/
theorem weak_duality {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ)
    (x u : Fin n → Fin T → ℝ) (z : Fin m → ℝ)
    (hP : Feasible I y v) (hD : DualFeasible I x u z) :
    obj I y v ≤ dualObj I x u z := by sorry

end OnlineOvertime.HOOPBOT
