-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_theorem_3
-- name    : NeedPersuasion.FullInfo.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:58.880753+00:00
-- url     : https://prove2.me/theorems/572847f2-59f1-411e-b890-e61b05c8abdc
-- title:
--   Theorem 3, p. 15 — if L(π) < 0, π ∈ Π_SM is Pareto-efficient within Π_SM iff within Π_AP
-- statement:
--   Assume the standing assumptions. Let $\pi\in\Pi_{SM}$ be a signaling mechanism for which the obedience constraint (LEAVE) does not bind,
--   $$L(\pi)=\sum_{n\ge0}(\lambda\pi_n-\pi_{n+1})u_L(n)<0 .$$
--   Then $\pi$ is Pareto-efficient within $\Pi_{SM}$ if and only if it is Pareto-efficient within $\Pi_{AP}$.
--
--   The theorem identifies (LEAVE) as the only incentive constraint that can separate the signaling frontier from the first-best frontier; it is the bridge used in Theorem 4.
-- source:
--   arXiv:2005.07253v3, Theorem 3, p. 15

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem theorem_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiSM M)
    (hL : leaveVal M π < 0) :
    ParetoEfficientIn M (PiSM M) π ↔ ParetoEfficientIn M (PiAP M) π := by sorry

end NeedPersuasion.FullInfo
