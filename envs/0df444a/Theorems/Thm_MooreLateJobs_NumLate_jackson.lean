-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_jackson
-- name    : MooreLateJobs.NumLate.jackson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:06:34.070073+00:00
-- url     : https://prove2.me/theorems/69321590-cdd2-468a-a127-f66c8af80cbf
-- title:
--   Lemma (Jackson) — a schedule with no late job exists iff the due-date order has none
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge0$ and due-dates $D_j$ with $t_j\le D_j$. There exists a schedule of $J$ having no late jobs if and only if every schedule of $J$ ordered according to the due-dates,
--   $$
--   D_{i_1}\le D_{i_2}\le\cdots\le D_{i_n},
--   $$
--   has no late jobs.
--
--   This is the earliest-due-date rule for feasibility (Jackson 1955); Moore uses it to reorder the early jobs of an optimal schedule and to certify the final schedule.
--
--   **Formalization Note** Ties in the due-dates are broken arbitrarily, so the right-hand side quantifies over every due-date ordered schedule. $t_j\ge0$ is added (the statement fails for negative processing times: with $t=(1,1,-10)$ and $D=(1,1.5,2)$ the due-date order has a late job while the order $(3,1,2)$ has none); $t_j\le D_j$ is the paper's standing assumption.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Lemma (Jackson)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

theorem jackson {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i) :
    (∃ S : List ι, Shared.IsSchedule J S ∧ lateSet t D S = ∅) ↔
      ∀ S : List ι, Shared.IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) →
        lateSet t D S = ∅ := by sorry

end MooreLateJobs.NumLate
