-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_theorem_1
-- name    : NeedPersuasion.FullInfo.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:01.278989+00:00
-- url     : https://prove2.me/theorems/822e0421-236d-47c9-9d43-41da3203af5a
-- title:
--   Theorem 1, p. 14 — every Pareto-efficient signaling mechanism has a threshold structure with threshold ≤ m_fi
-- statement:
--   Assume the standing assumptions. Let $\pi\in\Pi_{SM}$ be Pareto-efficient within the class $\Pi_{SM}$ of signaling mechanisms. Then $\pi$ has a threshold structure with a finite threshold $x=m+a$ satisfying
--   $$x\le m_{fi}.$$
--   That is, there is $m\in\mathbb N_0$ with $\pi_{k+1}=\lambda\pi_k$ for $k<m$, $\pi_{k+1}=\lambda_H\pi_k$ for $k>m$, and $m+(\pi_{m+1}-\lambda_H\pi_m)/(\lambda_L\pi_m)\le m_{fi}$.
--
--   Theorem 1 reduces the search for efficient signaling mechanisms to a one-parameter family of threshold policies, which is how every welfare comparison of the paper is carried out.
--
--   **Formalization Note** The conclusion requires a finite $m$, so it also excludes the threshold $\infty$ ("join regardless of the queue length").
-- source:
--   arXiv:2005.07253v3, Theorem 1, p. 14

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem theorem_1 (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hPE : ParetoEfficientIn M (PiSM M) π) :
    HasThresholdAtMost M π (mfi M) := by sorry

end NeedPersuasion.FullInfo
