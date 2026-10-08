-- Prove2me | Theorems.Thm_MatousekLP_Scheduling_lpr_topt_le
-- name    : MatousekLP.Scheduling.lpr_topt_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:39:48.476999+00:00
-- url     : https://prove2.me/theorems/8ae008cc-c973-4b4d-af69-ae3e01620d17
-- title:
--   Proof of Theorem 8.3.4 — LPR(t_opt) is feasible and t*(t_opt) ≤ t_opt
-- statement:
--   Let $d_{ij} > 0$ be running times of $n$ jobs on $m$ machines, and let $\sigma_{\mathrm{opt}}$ be an optimal schedule, with makespan $t_{\mathrm{opt}}$. Then:
--
--   1. the linear program $\mathrm{LPR}(t_{\mathrm{opt}})$ is feasible, and
--   2. every optimal solution $(t, x)$ of $\mathrm{LPR}(t_{\mathrm{opt}})$ has value
--   $$
--   t \le t_{\mathrm{opt}}, \qquad\text{that is,}\qquad t^*(t_{\mathrm{opt}}) \le t_{\mathrm{opt}} .
--   $$
--
--   This says that the relaxation with threshold $T = t_{\mathrm{opt}}$ is a genuine relaxation of the scheduling problem; it is the first inequality used to compare the rounded schedule with the optimum.
--
--   **Formalization Note** The optimal value $t^*(t_{\mathrm{opt}})$ is expressed through optimal solutions of $\mathrm{LPR}(t_{\mathrm{opt}})$, not through an infimum.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 155, proof of Theorem 8.3.4

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation

namespace MatousekLP.Scheduling

/-- Proof of Theorem 8.3.4 (Matoušek–Gärtner, p. 155): with `t_opt` the makespan of an
optimal schedule, the relaxation `LPR(t_opt)` is feasible, and every optimal solution
`(t, x)` of `LPR(t_opt)` has value `t ≤ t_opt` (that is, `t*(t_opt) ≤ t_opt`). -/
theorem lpr_topt_le {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (σopt : Fin n → Fin m) (hσopt : IsOptimalSchedule d σopt) :
    (∃ (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ), LPRFeasible d (makespan d σopt) t x) ∧
      ∀ (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ),
        LPROptimal d (makespan d σopt) t x → t ≤ makespan d σopt := by sorry

end MatousekLP.Scheduling
