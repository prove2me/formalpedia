-- Prove2me | Theorems.Thm_MooreLateJobs_MaxDeferral_bounded_exists_feasible_level
-- name    : MooreLateJobs.MaxDeferral.bounded_exists_feasible_level
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:37:01.800369+00:00
-- url     : https://prove2.me/theorems/e34bc8e1-b1e5-4b46-aad4-17b4daaeae0c
-- title:
--   Bounded costs give a level $y>0$ at which $S_D(y)$ has no late jobs
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge 0$ and continuous, bounded, non-decreasing deferral costs $P_j$. For each $y>0$ let $S_D(y)$ be a schedule of $J$ ordered by non-decreasing due-dates $D_j=P_j^*(y)$ (ties broken arbitrarily). Then
--
--   $$
--   \exists\, y>0:\quad S_D(y) \text{ has no late jobs, i.e. } C_j\le P_j^*(y) \text{ for every job } j.
--   $$
--
--   This supplies the feasible level from which the least feasible level $y^*$ is obtained.
--
--   **Formalization Note** The family $y\mapsto S_D(y)$ is an arbitrary one satisfying the ordering condition for every $y>0$, so every tie-break is covered. $t_j\ge0$ is added (processing times are durations).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, pp. 108-109, "Minimizing the Maximum Deferral Cost" ("In that the P_i's are bounded, there always exists y > 0 such that S_D(y) has no "late" jobs")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt

namespace MooreLateJobs.MaxDeferral

theorem bounded_exists_feasible_level {ι : Type*} [DecidableEq ι] (J : Finset ι) (t : ι → ℝ)
    (P : ι → ℝ → ℝ) (ht : ∀ i ∈ J, 0 ≤ t i)
    (hcont : ∀ i ∈ J, Continuous (P i)) (hbdd : ∀ i ∈ J, ∃ M, ∀ s, |P i s| ≤ M)
    (hmono : ∀ i ∈ J, Monotone (P i)) (SD : ℝ → List ι)
    (hSD : ∀ y, 0 < y →
      Shared.IsSchedule J (SD y) ∧ (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y)) :
    ∃ y, 0 < y ∧ NoLateAt t P y (SD y) := by sorry

end MooreLateJobs.MaxDeferral
