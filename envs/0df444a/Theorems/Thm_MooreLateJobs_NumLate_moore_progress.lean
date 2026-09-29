-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_moore_progress
-- name    : MooreLateJobs.NumLate.moore_progress
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:10:07.366974+00:00
-- url     : https://prove2.me/theorems/71289d61-9641-489d-bd0b-abd86a1f46d6
-- title:
--   p. 108 — Moore's algorithm can always proceed while a late job remains
-- statement:
--   Let $J$ be a finite set of jobs with $t_j\ge0$ and $t_j\le D_j$, and let $l_0$ be a schedule of $J$ in shortest-processing-time order ($t$ non-decreasing, ties arbitrary). If a state $(\text{cur},\text{rej})$ is reached from $(l_0,\emptyset)$ by passes of Steps 2–3 and the current sequence still has a late job, then another pass of Steps 2–3 applies to it.
--
--   Together with termination, this shows that every run of the algorithm ends in a state whose current sequence has no late job.
--
--   **Formalization Note** Steps 2–3 are the relation `MooreStep`; runs are its reflexive-transitive closure. $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 108, paragraph after the proof of case 3) ("This process continues ...")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_MooreStep

namespace MooreLateJobs.NumLate

theorem moore_progress {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (l₀ : List ι) (hl₀ : Shared.IsSchedule J l₀) (hspt : l₀.Pairwise (fun a b => t a ≤ t b))
    (cur rej : List ι) (hrun : Relation.ReflTransGen (MooreStep t D) (l₀, []) (cur, rej))
    (hlate : (lateSet t D cur).Nonempty) :
    ∃ s' : List ι × List ι, MooreStep t D (cur, rej) s' := by sorry

end MooreLateJobs.NumLate
