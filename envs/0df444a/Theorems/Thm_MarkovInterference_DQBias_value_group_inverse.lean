-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_value_group_inverse
-- name    : MarkovInterference.DQBias.value_group_inverse
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:48.108782+00:00
-- url     : https://prove2.me/theorems/0bc3c807-ac2a-4be2-af1f-2468ccafc7a4
-- title:
--   §3.3 — relative value equals the group inverse applied to reward
-- statement:
--   For a primitive experiment transition matrix $P_{1/2}$ with stationary law $\rho_{1/2}$, let $r_{1/2}$ be its mean reward vector and $\bar r=\rho_{1/2}^{\top}r_{1/2}$. The excess-reward series converges as a vector, and its sum is
--
--   $$V_{1/2}=\sum_{t=0}^{\infty}(P_{1/2}^{t}r_{1/2}-\bar r\mathbf1)=(I-P_{1/2})^\#r_{1/2}.$$
--
--   This identifies the paper's reward-to-go value with the matrix quantity used in its perturbation expansion.
--
--   **Formalization Note** The theorem states convergence as `HasSum` as well as the equality for the defined total sum. This rules out Lean's zero default for a nonsummable series.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, p. 15, §3.3, the well-known fact following Eq. (6)

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP

namespace MarkovInterference.DQBias

/-- §3.3, p. 15: the excess-reward series equals the group-inverse value vector. -/
theorem value_group_inverse {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S) (rho : S → ℝ)
    (hp : IsPrimitive M.Phalf) (hrho : IsStationaryDist M.Phalf rho) :
    HasSum (fun t : ℕ => (M.Phalf ^ t).mulVec M.rHalf -
      (fun _ => M.avgReward rho)) ((groupInv M.Phalf rho).mulVec M.rHalf) ∧
    M.V rho = (groupInv M.Phalf rho).mulVec M.rHalf := by sorry

end MarkovInterference.DQBias
