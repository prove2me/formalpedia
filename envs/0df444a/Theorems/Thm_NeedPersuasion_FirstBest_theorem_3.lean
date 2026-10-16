-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_theorem_3
-- name    : NeedPersuasion.FirstBest.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:56.620997+00:00
-- url     : https://prove2.me/theorems/991292d0-96e2-4138-83e6-ee6f81615ea1
-- title:
--   Theorem 3, p. 15 — if (LEAVE) does not bind, L(π) < 0, then π is Pareto-efficient in Π_SM iff it is in Π_AP
-- statement:
--   Let $\pi\in\Pi_{SM}$ be a signaling mechanism whose (LEAVE) constraint does not bind:
--   $$L(\pi)=\sum_{n\ge0}(\lambda\pi_n-\pi_{n+1})u_L(n)<0 .$$
--   Then $\pi$ is Pareto-efficient within $\Pi_{SM}$ if and only if it is Pareto-efficient within $\Pi_{AP}$.
--
--   The result identifies (LEAVE) as the only obedience constraint that can separate efficient signaling mechanisms from efficient admission policies.
-- source:
--   arXiv:2005.07253v3, Theorem 3, p. 15

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model

namespace NeedPersuasion.FirstBest

theorem theorem_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiSM M)
    (hL : leaveVal M π < 0) :
    ParetoEfficientIn M (PiSM M) π ↔ ParetoEfficientIn M (PiAP M) π := by sorry

end NeedPersuasion.FirstBest
