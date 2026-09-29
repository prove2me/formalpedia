-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_lemma1
-- name    : MooreLateJobs.NumLate.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:06:08.240754+00:00
-- url     : https://prove2.me/theorems/87caeade-fb29-46aa-835c-28f61c3f84f0
-- title:
--   Lemma 1 — an optimal schedule is equivalent to (A, R) and to every (A, P)
-- statement:
--   Let $J$ be a finite set of jobs with processing times $t_j\ge 0$ and due-dates $D_j$ satisfying $t_j\le D_j$. Let $S$ be an optimal schedule for $J$, with ordered early set $A$ and ordered late set $R$. Then
--   $$
--   |L(A,R)|=|L(S)|\quad\text{and}\quad |L(A,P)|=|L(S)|\ \text{ for every permutation } P \text{ of } R.
--   $$
--
--   So every optimal schedule can be rearranged, without changing its number of late jobs, so that all its early jobs come first (in their original order) followed by its late jobs in any order.
--
--   **Formalization Note** $t_j\ge0$ is added: processing times are durations, and the paper never states it. $t_j\le D_j$ is the paper's standing assumption (p. 102).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Lemma 1

import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma1 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) :
    (lateSet t D (earlyPart t D S ++ latePart t D S)).card = (lateSet t D S).card ∧
    ∀ P : List ι, P.Perm (latePart t D S) →
      (lateSet t D (earlyPart t D S ++ P)).card = (lateSet t D S).card := by sorry

end MooreLateJobs.NumLate
