-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_lemma2
-- name    : MooreLateJobs.NumLate.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:07:13.172531+00:00
-- url     : https://prove2.me/theorems/09e7d4b9-f84a-4d30-95d8-99ec9a713ced
-- title:
--   Lemma 2 — reordering A by due-dates keeps an optimal (A, R) schedule optimal
-- statement:
--   Let $J$ be a finite set of jobs with $t_j\ge0$ and $t_j\le D_j$. Let $S$ be an optimal schedule for $J$ of the form $(A,R)$, and let $A_D$ be $A$ re-ordered according to the due-date rule ($D$ non-decreasing, ties arbitrary). Then
--   $$
--   S_D=(A_D,R)
--   $$
--   is an optimal schedule for $J$, with the same late set as $S$ (the jobs of $A_D$ are early and those of $R$ are late).
--
--   **Formalization Note** "Of the form $(A,R)$" is the equation $S=A\,R$ (list concatenation). The conclusion includes that the late set of $S_D$ equals that of $S$, which is what the notation $S_D=(A_D,R)$ asserts. $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Lemma 2

import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma2 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) (hform : S = earlyPart t D S ++ latePart t D S)
    (AD : List ι) (hAD : AD.Perm (earlyPart t D S)) (hdd : AD.Pairwise (fun a b => D a ≤ D b)) :
    IsOptimal t D J (AD ++ latePart t D S) ∧
      lateSet t D (AD ++ latePart t D S) = lateSet t D S := by sorry

end MooreLateJobs.NumLate
