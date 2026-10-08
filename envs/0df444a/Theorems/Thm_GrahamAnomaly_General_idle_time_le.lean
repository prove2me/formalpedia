-- Prove2me | Theorems.Thm_GrahamAnomaly_General_idle_time_le
-- name    : GrahamAnomaly.General.idle_time_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:03:28.856975+00:00
-- url     : https://prove2.me/theorems/1b2a58fd-78a3-4b2a-a46a-1a3081ebc66e
-- title:
--   (2) and (5), proof of Theorem 1, p. 420 — idle processor time is bounded by the covering chain
-- statement:
--   Consider a feasible schedule of tasks with positive durations $\mu'(T_j)$ on $n'\ge1$ identical processors. Suppose a $\prec'$-chain $C$ of tasks covers every time before its finishing time $\omega'$ at which some processor is idle. Then the total idle processor time obeys
--
--   $$n'\omega'-\sum_j\mu'(T_j)\le(n'-1)\sum_{T_j\in C}\mu'(T_j).$$
--
--   This is Graham's display (2), with the idle-time accounting identity of display (5) substituted into its left side. It converts the covering property into a numerical bound.
--
--   **Formalization Note** The chain is a list in precedence order. The expression on the left equals the sum of durations of all empty tasks in the timing diagram. Once coverage is assumed, the numerical estimate needs only schedule feasibility, not the list rule.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 420, displays (2) and (5), proof of Theorem 1; https://doi.org/10.1137/0117039

import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Display (2), using the empty-task-time identity in (5). -/
theorem idle_time_le {r n' : ℕ} (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (G' : Schedule n' μ' prec') (c : List (Fin r))
    (hc : c.Chain' prec')
    (hcover : ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
      ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a) :
    (n' : ℝ) * G'.finish - ∑ j, μ' j ≤
      ((n' : ℝ) - 1) * (c.map μ').sum := by sorry

end GrahamAnomaly.General
