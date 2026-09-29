-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_lemma3
-- name    : MooreLateJobs.NumLate.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:07:45.954812+00:00
-- url     : https://prove2.me/theorems/33606c06-035b-4de9-a2cd-2558b4fdaa6e
-- title:
--   Lemma 3 — removing late jobs of an optimal schedule preserves optimality
-- statement:
--   Let $J$ be a finite set of jobs with $t_j\ge0$ and $t_j\le D_j$. Suppose $S$ is an optimal schedule for $J$ whose late set $L$ is non-empty, and let $J^*\subseteq L$. Let $S'$ be any optimal schedule for $J'=J\setminus J^*$ of the form $(A',R')$, with late set $L'$. Then for every ordering $P''$ of $J^*\cup L'$ the schedule
--   $$
--   S''=(A',P'')
--   $$
--   is an optimal schedule for $J$, and its late set is exactly $L''=J^*\cup L'$.
--
--   This lemma is what lets the algorithm discard jobs one by one: a job found late in some optimal schedule can be set aside, the rest scheduled optimally, and the discarded job appended.
--
--   **Formalization Note** $t_j\ge0$ is added. The hypothesis that $L$ is non-empty is kept as on the page.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Lemma 3 (proof pp. 105-106)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma3 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) (hL : (lateSet t D S).Nonempty)
    (Jstar : Finset ι) (hJstar : Jstar ⊆ lateSet t D S)
    (S' : List ι) (hS' : IsOptimal t D (J \ Jstar) S')
    (hform : S' = earlyPart t D S' ++ latePart t D S')
    (P'' : List ι) (hP'' : Shared.IsSchedule (Jstar ∪ lateSet t D S') P'') :
    IsOptimal t D J (earlyPart t D S' ++ P'') ∧
      lateSet t D (earlyPart t D S' ++ P'') = Jstar ∪ lateSet t D S' := by sorry

end MooreLateJobs.NumLate
