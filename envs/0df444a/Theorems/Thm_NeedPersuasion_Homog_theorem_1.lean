-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_theorem_1
-- name    : NeedPersuasion.Homog.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:58.845842+00:00
-- url     : https://prove2.me/theorems/e3dda039-7796-4d76-a97b-b9d133bb2ea1
-- title:
--   Theorem 1, p. 14 — every Pareto-efficient signaling mechanism has a threshold structure with threshold ≤ m_fi
-- statement:
--   Consider the congested-service model under its standing assumptions. Let $\pi \in \Pi_{SM}$ be a signaling mechanism (a distribution satisfying the detailed-balance and obedience constraints) which is Pareto-efficient within the class $\Pi_{SM}$: no $\hat\pi \in \Pi_{SM}$ has $W_L(\hat\pi) \ge W_L(\pi)$ and $W_H(\hat\pi) \ge W_H(\pi)$ with one inequality strict. Then $\pi$ has a threshold structure with a finite threshold not exceeding the full-information threshold: there is $m \in \mathbb N_0$ with
--   $$\pi_{k+1} = \lambda\pi_k \ (k < m), \qquad \pi_{k+1} = \lambda_H \pi_k \ (k > m), \qquad m + \frac{\pi_{m+1} - \lambda_H\pi_m}{\lambda_L \pi_m} \le m_{fi}.$$
--
--   Low-need users are therefore told to join below some queue length and to leave above it, and the cutoff is never later than under full information. In this mission the theorem places the optimal signaling mechanism's threshold below $m_{fi}$.
--
--   **Formalization Note** The conclusion excludes the threshold $\infty$ (always join), which the paper's "threshold less than or equal to $m_{fi}$" excludes as well.
-- source:
--   arXiv:2005.07253v3, Theorem 1, p. 14; proof App. A, pp. 34–36

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

theorem theorem_1 (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hπ : ParetoEfficientIn M (PiSM M) π) :
    HasThresholdAtMost M π (mfi M) := by sorry

end NeedPersuasion.Homog
