-- Prove2me | Theorems.Thm_MooreLateJobs_MaxDeferral_jackson
-- name    : MooreLateJobs.MaxDeferral.jackson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:35:16.488375+00:00
-- url     : https://prove2.me/theorems/d12146aa-79d1-4127-8bb0-5d432711b13c
-- title:
--   Lemma (Jackson) — a schedule with no late jobs exists iff every due-date ordering has none
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge0$ and due-dates $D_j\in\mathbb R\cup\{\pm\infty\}$, processed on one machine starting at time $0$. Then
--
--   $$
--   \exists\, S \text{ schedule of } J \text{ with no late jobs}
--   \iff
--   \text{every schedule of } J \text{ ordered by non-decreasing } D \text{ has no late jobs}.
--   $$
--
--   This is Jackson's lemma as used by Moore: the due-date (earliest-due-date) schedule decides feasibility. In the section on maximum deferral cost it is applied with the due-dates $D_i=P_i^*(y)$, some of which are $0$ or $+\infty$.
--
--   **Formalization Note** Two changes relative to the page, both generalizations. (i) Due-dates are extended reals; real due-dates, the page's setting, embed. (ii) The paper's standing assumption $t_i\le D_i$ (p. 102) is not assumed: the deferral-cost problem has no given due-dates, and the lemma holds without it. The hypothesis $t_j\ge 0$ (processing times are durations) is added; the page never writes it, and the lemma is false for negative times. Ties among equal due-dates are arbitrary: the right-hand side quantifies over every due-date ordering.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Lemma (Jackson); used on p. 108 ("Jackson's lemma can now be used to find an optimal schedule")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt

namespace MooreLateJobs.MaxDeferral

theorem jackson {ι : Type*} [DecidableEq ι] (J : Finset ι) (t : ι → ℝ) (D : ι → EReal)
    (ht : ∀ i ∈ J, 0 ≤ t i) :
    (∃ S : List ι, Shared.IsSchedule J S ∧ NoLate t D S) ↔
      ∀ S : List ι, Shared.IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) → NoLate t D S := by sorry

end MooreLateJobs.MaxDeferral
