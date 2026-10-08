-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_lawler_rule_optimal
-- name    : LawlerPrec.MinMax.lawler_rule_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:44:04.103895+00:00
-- url     : https://prove2.me/theorems/328dfa31-ce00-4056-8fdc-9b7ecaa8244c
-- title:
--   §3 Sequencing Algorithm, p. 545 — every sequence built by placing last a least-cost eligible job is minmax optimal
-- statement:
--   Suppose a nonempty finite set $J$ of jobs is to be processed by a single machine, one at a time with no interruptions, subject to arbitrary given precedence constraints. Job $j$ has a non-negative processing time $a_j$ and a monotone nondecreasing cost function $c_j(t)$, the cost incurred when $j$ is completed at time $t$.
--
--   Build a sequence from last position to first: among the jobs not yet placed, $P$, choose a job required to precede none of the other jobs of $P$ whose cost $c_j(T_P)$ at $T_P = \sum_{i \in P} a_i$ is least (ties broken arbitrarily), place it in the latest open position, and repeat. Then every sequence $\pi$ so produced is **minmax optimal**: it observes the precedence constraints, and
--
--   $$
--   \max_{j \in J} c_j\bigl(C_j(\pi)\bigr) \;\le\; \max_{j \in J} c_j\bigl(C_j(\pi')\bigr)
--   $$
--
--   for every sequence $\pi'$ of $J$ that observes the precedence constraints, where $C_j$ denotes completion times with the machine starting at time $0$ and no idle time.
--
--   This is the efficient algorithm that Lawler's paper derives from its Sequencing Theorem. It solves the single-machine problem of minimizing the maximum of nondecreasing job costs under arbitrary precedence constraints, which includes minimizing maximum lateness and maximum tardiness, and it generalizes Moore's procedure for the case without precedence constraints.
--
--   **Formalization Note** "Produced by the rule" is `IsLawlerSequence`, a property of the finished sequence quantifying over every tie-break. Feasibility of the rule's sequence is part of the conclusion, not a hypothesis. Non-negative processing times are an added, disclosed hypothesis: the paper's processing times are durations and its exchange argument needs them. The maximum cost is the published `MooreLateJobs.MaxDeferral.maxCost`, applied with Lawler's costs $c_j$; Moore's continuity and boundedness assumptions are not assumed.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 545, §3 Sequencing Algorithm, first paragraph ("An efficient algorithm for finding a minmax optimal sequence follows immediately from the theorem above")

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsMinmaxOptimal
import Definitions.Def_LawlerPrec_MinMax_IsLawlerSequence

namespace LawlerPrec.MinMax

/-- §3 Sequencing Algorithm, p. 545 (Lawler 1973): every sequence of the nonempty job set `J`
produced by repeatedly placing last, among the remaining jobs, a job that is required to precede
none of them and has the least cost at the remaining jobs' total processing time (ties broken
arbitrarily) is minmax optimal: it observes the precedence constraints and its maximum incurred
cost is no greater than that of any sequence of `J` observing them. Processing times are
non-negative and costs monotone nondecreasing. -/
theorem lawler_rule_optimal {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (l : List ι) (hl : MooreLateJobs.Shared.IsSchedule J l)
    (hrule : IsLawlerSequence a c prec l) :
    IsMinmaxOptimal a c prec J hJ l := by sorry

end LawlerPrec.MinMax
