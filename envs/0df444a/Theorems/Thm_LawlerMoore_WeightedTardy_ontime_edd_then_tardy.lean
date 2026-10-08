-- Prove2me | Theorems.Thm_LawlerMoore_WeightedTardy_ontime_edd_then_tardy
-- name    : LawlerMoore.WeightedTardy.ontime_edd_then_tardy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:21.623469+00:00
-- url     : https://prove2.me/theorems/f611c173-c5f5-43d8-97a6-fd5bb8979a18
-- title:
--   Section 5 — on-time jobs in deadline order, then the tardy jobs in arbitrary order
-- statement:
--   Consider $n$ jobs on a single machine with nonnegative integer processing times $a'_j$, nonnegative integer deadlines $d_j$ and penalties $p_j \ge 0$, and let $W(\sigma)$ be the weighted number of tardy jobs of a sequence $\sigma$ (the sum of $p_j$ over the jobs completed after their deadlines).
--
--   Let $\sigma$ be any sequence of all the jobs, and let $E$ be the set of jobs that are on time in $\sigma$. Then there is an ordering $\varepsilon$ of $E$ in nondecreasing order of deadlines such that, for **every** sequence of the form
--   $$
--   \sigma' = (\varepsilon, \lambda),
--   $$
--   in which $\lambda$ lists the remaining (tardy) jobs in an arbitrary order,
--   1. every job of $E$ is on time in $\sigma'$, and
--   2. $W(\sigma') \le W(\sigma)$.
--
--   This is the structural observation of Section 5: one can assume that the on-time jobs are sequenced in order of their deadlines, with the tardy jobs following them in arbitrary order, so that the problem reduces to choosing the set of on-time jobs.
--
--   **Formalization Note** Jobs are `Fin n`; sequences are lists, and a schedule is a duplicate-free list of all jobs (`IsSchedule Finset.univ`). Tardiness is the published `lateSet` (strictly $C_j > d_j$). The penalties are assumed nonnegative ("a penalty $p_j$ is exacted"), which the inequality needs. No ordering of the job indices by deadline is assumed here.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 79, Section 5

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared MooreLateJobs.NumLate

/-- §5 (p. 79): the on-time jobs of any sequence `l`, sequenced in order of their deadlines and
followed by the tardy jobs in arbitrary order, stay on time, and the weighted number of tardy
jobs does not increase (penalties `p j ≥ 0`). -/
theorem ontime_edd_then_tardy {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ E : List (Fin n),
      E.Nodup ∧
      (∀ j, j ∈ E ↔ j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) l) ∧
      E.Pairwise (fun i j => d i ≤ d j) ∧
      ∀ L : List (Fin n), IsSchedule Finset.univ (E ++ L) →
        (∀ j ∈ E, j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) (E ++ L)) ∧
        weightedTardy a' d p (E ++ L) ≤ weightedTardy a' d p l := by sorry

end LawlerMoore.WeightedTardy
