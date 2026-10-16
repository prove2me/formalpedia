-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_theorem_2
-- name    : NeedPersuasion.FullInfo.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:07.15989+00:00
-- url     : https://prove2.me/theorems/9276b9c5-6689-4523-93c6-10a630f01c46
-- title:
--   Theorem 2, p. 15 — every Pareto-efficient admission policy has a threshold structure with threshold ≤ m_fi
-- statement:
--   Assume the standing assumptions. Let $\pi\in\Pi_{AP}$ be Pareto-efficient within the class $\Pi_{AP}$ of admission policies. Then $\pi$ has a threshold structure with a finite threshold $x=m+a$ satisfying
--   $$x\le m_{fi}.$$
--
--   This is the analogue of Theorem 1 for the first-best benchmark, where the provider enforces joining and leaving and the obedience constraints are dropped. It is used to show that a non-efficient admission policy is dominated by a threshold policy.
--
--   **Formalization Note** As in Theorem 1, the threshold must be finite.
-- source:
--   arXiv:2005.07253v3, Theorem 2, p. 15

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem theorem_2 (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hPE : ParetoEfficientIn M (PiAP M) π) :
    HasThresholdAtMost M π (mfi M) := by sorry

end NeedPersuasion.FullInfo
