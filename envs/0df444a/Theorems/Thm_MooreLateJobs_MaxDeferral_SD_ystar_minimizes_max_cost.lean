-- Prove2me | Theorems.Thm_MooreLateJobs_MaxDeferral_SD_ystar_minimizes_max_cost
-- name    : MooreLateJobs.MaxDeferral.SD_ystar_minimizes_max_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:38:15.035974+00:00
-- url     : https://prove2.me/theorems/905b689d-ec25-4228-ba71-453d3cbe5065
-- title:
--   The due-date schedule $S_D(y^*)$ has minimal maximum deferral cost
-- statement:
--   Let $J$ be a nonempty finite set of jobs with processing times $t_j\ge 0$, processed on one machine from time $0$, and let each job have a continuous, bounded, non-decreasing deferral cost $P_j$, where $P_j(s)$ is the cost of completing $j$ at time $s$. For each $y>0$ let $S_D(y)$ be a schedule of $J$ ordered by non-decreasing due-dates $D_j=P_j^*(y)$ (ties broken arbitrarily). Let $y^*>0$ be such that
--
--   1. $S_D(y^*)$ has no late jobs, and
--   2. for all $0<y<y^*$, $S_D(y)$ has at least one late job.
--
--   Then for every schedule $S$ of $J$,
--
--   $$
--   \max_{j\in J} P_j\bigl(C_j^{S_D(y^*)}\bigr)\;\le\;\max_{j\in J} P_j\bigl(C_j^{S}\bigr),
--   $$
--
--   where $C_j^{S}$ is the completion time of $j$ in $S$: the schedule $S_D(y^*)$ has minimal maximum deferral cost.
--
--   This reduces the single-machine min–max deferral cost problem to a one-parameter family of due-date sorts, searched over the cost level $y$.
--
--   **Formalization Note** $y^*$ is given together with its two defining properties; its existence is the separate milestone `exists_ystar`. The minimum is over all schedules of $J$, not only over the $S_D(y)$. The family $y\mapsto S_D(y)$ is arbitrary subject to the ordering condition, so every tie-break is covered. "For all $y<y^*$" is read as $0<y<y^*$. Times are measured from $0$, and $P_j^*$ is computed over times $s\ge0$ (see the definition of $P^*$). $t_j\ge0$ is added (processing times are durations).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 109, "Minimizing the Maximum Deferral Cost", last sentence ("The schedule S_D(y*) has minimal maximum deferral cost.")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt
import Definitions.Def_MooreLateJobs_MaxDeferral_maxCost

namespace MooreLateJobs.MaxDeferral

theorem SD_ystar_minimizes_max_cost {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (hJ : J.Nonempty) (t : ι → ℝ) (P : ι → ℝ → ℝ) (ht : ∀ i ∈ J, 0 ≤ t i)
    (hcont : ∀ i ∈ J, Continuous (P i)) (hbdd : ∀ i ∈ J, ∃ M, ∀ s, |P i s| ≤ M)
    (hmono : ∀ i ∈ J, Monotone (P i)) (SD : ℝ → List ι)
    (hSD : ∀ y, 0 < y →
      Shared.IsSchedule J (SD y) ∧ (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y))
    (ystar : ℝ) (hystar : 0 < ystar) (h1 : NoLateAt t P ystar (SD ystar))
    (h2 : ∀ y, 0 < y → y < ystar → ¬ NoLateAt t P y (SD y)) :
    ∀ l : List ι, Shared.IsSchedule J l → maxCost t P J hJ (SD ystar) ≤ maxCost t P J hJ l := by sorry

end MooreLateJobs.MaxDeferral
