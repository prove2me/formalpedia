-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_repeated_elimination_optimal
-- name    : MooreLateJobs.NumLate.repeated_elimination_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:08:18.164301+00:00
-- url     : https://prove2.me/theorems/6c414d76-a09d-46bd-ad44-aac57c954808
-- title:
--   Theoretical Development, p. 106 — eliminating jobs late in optimal schedules yields (A_D, P)
-- statement:
--   Let $J$ be a finite set of jobs with $t_j\ge0$ and $t_j\le D_j$. Let $J_{i_1},\dots,J_{i_q}$ be distinct jobs of $J$ eliminated one at a time, so that for each $k$ the job $J_{i_{k+1}}$ is late in some optimal schedule for $J\setminus\{J_{i_1},\dots,J_{i_k}\}$. Write $J^*=\{J_{i_1},\dots,J_{i_q}\}$ and suppose $J\setminus J^*$ admits a schedule with no late job. Let $A_D$ be the jobs of $E=J\setminus J^*$ ordered according to the due-date rule and $P$ any ordering of $J^*$. Then
--   $$
--   S=(A_D,P)
--   $$
--   is an optimal schedule for $J$.
--
--   This reduces the problem to finding, repeatedly, a job that is late in some optimal schedule.
--
--   **Formalization Note** "The algorithm fails to find a job in $J-J^*$" is encoded as feasibility of $J\setminus J^*$ (a schedule with no late job); the due-date schedule $A_D$ is any due-date ordered schedule of $J\setminus J^*$ (ties arbitrary). $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 106, Theoretical Development, paragraph after the proof of Lemma 3

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal

namespace MooreLateJobs.NumLate

theorem repeated_elimination_optimal {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (rej : List ι) (hnd : rej.Nodup) (hsub : ∀ j ∈ rej, j ∈ J)
    (hfound : ∀ (k : ℕ) (hk : k < rej.length), ∃ S : List ι,
      IsOptimal t D (J \ (rej.take k).toFinset) S ∧ rej[k] ∈ lateSet t D S)
    (hfeas : ∃ S : List ι, Shared.IsSchedule (J \ rej.toFinset) S ∧ lateSet t D S = ∅)
    (AD : List ι) (hAD : Shared.IsSchedule (J \ rej.toFinset) AD)
    (hdd : AD.Pairwise (fun a b => D a ≤ D b))
    (P : List ι) (hP : P.Perm rej) :
    IsOptimal t D J (AD ++ P) := by sorry

end MooreLateJobs.NumLate
