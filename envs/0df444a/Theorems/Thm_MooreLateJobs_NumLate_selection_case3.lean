-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_selection_case3
-- name    : MooreLateJobs.NumLate.selection_case3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:09:21.334962+00:00
-- url     : https://prove2.me/theorems/dc0f3b35-cec8-49d3-a5b1-508aa1681467
-- title:
--   Selection Algorithm, case 3), p. 107 — if a later job becomes late, J_q is late in some optimal schedule
-- statement:
--   Same setting as case 2): $J_c$ with $t_j\ge0$, $t_j\le D_j$; early due-date ordered jobs $J_{i_1},\dots,J_{i_{q-1}}$ with $t_{i_j}\le t_q\le t_b$ for all other jobs $J_b$; and $J_q$ inserted by the due-date rule,
--   $$
--   (J_{i_1}\cdots J_{i_k},\,J_q,\,J_{i_{k+1}}\cdots J_{i_{q-1}}),\qquad D_{i_1}\le\cdots\le D_{i_k}\le D_q\le D_{i_{k+1}}\le\cdots\le D_{i_{q-1}}.
--   $$
--   If $J_q$ is not late in this sequence but at least one of $J_{i_{k+1}},\dots,J_{i_{q-1}}$ is late, then $J_q\in L$ for some optimal schedule for $J_c$.
--
--   **Formalization Note** As for case 2). $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 107, Selection Algorithm, case 3) (proof pp. 107-108)

import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal

namespace MooreLateJobs.NumLate

theorem selection_case3 {ι : Type*} [DecidableEq ι] (Jc : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ Jc, 0 ≤ t i) (htD : ∀ i ∈ Jc, t i ≤ D i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (hearly : lateSet t D pre = ∅)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hqearly : q ∉ lateSet t D (pre.take k ++ q :: pre.drop k))
    (hlate : ∃ a ∈ pre.drop k, a ∈ lateSet t D (pre.take k ++ q :: pre.drop k)) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by sorry

end MooreLateJobs.NumLate
