-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_selection_case2
-- name    : MooreLateJobs.NumLate.selection_case2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:08:48.503551+00:00
-- url     : https://prove2.me/theorems/500fcedc-587c-49f4-8111-b39fda6db609
-- title:
--   Selection Algorithm, case 2), p. 107 — if J_q is late after insertion, J_q is late in some optimal schedule
-- statement:
--   Let $J_c$ be the finite set of jobs of the current sequence, with $t_j\ge0$ and $t_j\le D_j$ on $J_c$. Let $J_q\in J_c$ and let $(J_{i_1},\dots,J_{i_{q-1}})$ be distinct jobs of $J_c$ other than $J_q$ such that
--
--   1. $D_{i_1}\le\cdots\le D_{i_{q-1}}$ and all of $J_{i_1},\dots,J_{i_{q-1}}$ are early in this sequence;
--   2. $t_{i_j}\le t_q$ for $j=1,\dots,q-1$, and $t_q\le t_b$ for every other job $J_b$ of $J_c$;
--   3. $J_q$ is inserted according to the due-date rule, giving
--   $$
--   (J_{i_1}\cdots J_{i_k},\,J_q,\,J_{i_{k+1}}\cdots J_{i_{q-1}}),\qquad D_{i_1}\le\cdots\le D_{i_k}\le D_q\le D_{i_{k+1}}\le\cdots\le D_{i_{q-1}}.
--   $$
--
--   If $J_q$ is late in this inserted sequence, then $J_q\in L$ for some optimal schedule for $J_c$.
--
--   **Formalization Note** The setup's invariants (the first $q-1$ jobs are early and precede $J_q$ in the shortest-processing-time order) are hypotheses. That $J_q$ is late in the original current sequence is implied and not stated. $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, pp. 106-107, Selection Algorithm, case 2)

import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal

namespace MooreLateJobs.NumLate

theorem selection_case2 {ι : Type*} [DecidableEq ι] (Jc : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ Jc, 0 ≤ t i) (htD : ∀ i ∈ Jc, t i ≤ D i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (hearly : lateSet t D pre = ∅)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hlate : q ∈ lateSet t D (pre.take k ++ q :: pre.drop k)) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by sorry

end MooreLateJobs.NumLate
