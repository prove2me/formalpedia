-- Prove2me | Theorems.Thm_MooreLateJobs_MaxDeferral_exists_ystar
-- name    : MooreLateJobs.MaxDeferral.exists_ystar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:37:33.818984+00:00
-- url     : https://prove2.me/theorems/091613c2-b2e7-48d7-b379-2e8f22f045a6
-- title:
--   Existence of the least feasible cost level $y^*$
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge 0$ and continuous non-decreasing deferral costs $P_j$. For each $y>0$ let $S_D(y)$ be a schedule of $J$ ordered by non-decreasing due-dates $D_j=P_j^*(y)$. Assume
--
--   1. some level $y_1>0$ has $S_D(y_1)$ without late jobs, and
--   2. some level $y_0>0$ has $S_D(y_0)$ with at least one late job.
--
--   Then there is $y^*>0$ such that
--
--   $$
--   S_D(y^*) \text{ has no late jobs, and } S_D(y) \text{ has at least one late job for every } 0<y<y^*.
--   $$
--
--   The level $y^*$ is the least cost level at which the due-date schedule is feasible; the main theorem shows that $S_D(y^*)$ minimizes the maximum deferral cost.
--
--   **Formalization Note** Hypothesis 1 is the paper's footnote 3, which replaces boundedness ("It is sufficient if there exists $y>0$ such that $S_D(y)$ has no late jobs"); this is the stronger of the paper's two versions, and the bounded version follows from the milestone `bounded_exists_feasible_level`. Hypothesis 2 is **added**: without it the statement is false (with all costs identically $0$, $P_j^*(y)=+\infty$ for every $y>0$, every $S_D(y)$ is on time, and no $y^*>0$ has the second property). "For all $y<y^*$" is read as $0<y<y^*$, because $S_D(y)$ is defined only for $y>0$. $t_j\ge 0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 109, first paragraph (conditions 1) and 2) on y*) and footnote 3

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt

namespace MooreLateJobs.MaxDeferral

theorem exists_ystar {ι : Type*} [DecidableEq ι] (J : Finset ι) (t : ι → ℝ)
    (P : ι → ℝ → ℝ) (ht : ∀ i ∈ J, 0 ≤ t i)
    (hcont : ∀ i ∈ J, Continuous (P i)) (hmono : ∀ i ∈ J, Monotone (P i)) (SD : ℝ → List ι)
    (hSD : ∀ y, 0 < y →
      Shared.IsSchedule J (SD y) ∧ (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y))
    (hfeas : ∃ y₁, 0 < y₁ ∧ NoLateAt t P y₁ (SD y₁))
    (hinf : ∃ y₀, 0 < y₀ ∧ ¬ NoLateAt t P y₀ (SD y₀)) :
    ∃ ystar, 0 < ystar ∧ NoLateAt t P ystar (SD ystar) ∧
      ∀ y, 0 < y → y < ystar → ¬ NoLateAt t P y (SD y) := by sorry

end MooreLateJobs.MaxDeferral
