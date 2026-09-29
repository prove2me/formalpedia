-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_moore_algorithm_optimal
-- name    : MooreLateJobs.NumLate.moore_algorithm_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:11:28.037001+00:00
-- url     : https://prove2.me/theorems/1bfcb473-dc68-423c-99f5-7847b3825044
-- title:
--   The Algorithm, Step 2, p. 103 — Moore's algorithm terminates with a schedule minimizing the number of late jobs
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge0$ and due-dates $D_j$ with $t_j\le D_j$ for every job. Run Moore's algorithm:
--
--   1. (Step 1) Start from a schedule $l_0$ of $J$ in shortest-processing-time order, $t_{i_1}\le\cdots\le t_{i_n}$ (ties arbitrary), with no rejected jobs.
--   2. (Steps 2–3) Repeatedly find the first late job $J_{i_q}$ of the current sequence, reorder $J_{i_1},\dots,J_{i_q}$ by due-dates, and, if some job of that reordered prefix is late, reject $J_{i_q}$.
--
--   Suppose a run reaches a state whose current sequence has no late job, with rejected jobs $\mathrm{rej}$. Then for every ordering of the current sequence's jobs according to their due-dates, $A_D$, and every ordering $P$ of the rejected jobs,
--   $$
--   S=(A_D,P)
--   $$
--   is an optimal schedule for $J$: no schedule of $J$ has fewer late jobs.
--
--   This is the correctness theorem of Moore's algorithm for the single-machine problem of minimizing the number of late jobs ($1\|\sum U_j$).
--
--   **Formalization Note** The algorithm is the step relation `MooreStep` (every tie-break allowed); a run is its reflexive-transitive closure from $(l_0,[\,])$. $t_j\ge0$ is added (processing times are durations); $t_j\le D_j$ is the paper's standing assumption (p. 102). That the algorithm does reach such a state is stated separately (progress and termination).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 103, The Algorithm, Step 2 (proof pp. 104-108, Theoretical Development)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_MooreStep

namespace MooreLateJobs.NumLate

theorem moore_algorithm_optimal {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (l₀ : List ι) (hl₀ : Shared.IsSchedule J l₀) (hspt : l₀.Pairwise (fun a b => t a ≤ t b))
    (cur rej : List ι) (hrun : Relation.ReflTransGen (MooreStep t D) (l₀, []) (cur, rej))
    (hterm : lateSet t D cur = ∅)
    (cur' : List ι) (hcur' : cur'.Perm cur) (hdd : cur'.Pairwise (fun a b => D a ≤ D b))
    (rej' : List ι) (hrej' : rej'.Perm rej) :
    IsOptimal t D J (cur' ++ rej') := by sorry

end MooreLateJobs.NumLate
