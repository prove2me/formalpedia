-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_2_1_without_EDD
-- name    : LawlerCompress.TardyJobs.lemma_2_1_without_EDD
-- status  : Proved
-- author  : @0xbf
-- created : 2026-11-12T14:36:01.305206+00:00
-- url     : https://prove2.me/theorems/1c0cc126-ab23-4360-a881-e2f1cef398f5
-- title:
--   Canonical completion times form an interval without EDD
-- statement:
--   Let $I$ be any instance of the weighted tardy-jobs scheduling problem and let $j$ be one of its jobs. Without assuming that the jobs are listed in earliest-due-date order, the canonical completion times of $j$ still form an interval: there is an endpoint $a_j$ with $p_j\le a_j\le d_j+1$ such that
--
--   $$ar C_j=\{a_j,a_j+1,\ldots,d_j\},$$
--
--   with the convention that $a_j=d_j+1$ when $ar C_j$ is empty. Here $p_j$ and $d_j$ are the processing time and due date of job $j$, and $ar C_j$ is the set of times at which $j$ belongs to the canonical high-priority set. The result follows from the nesting of the eligible job sets as the time threshold increases; the EDD hypothesis used elsewhere in the paper is not needed for this interval property.
-- source:
--   K. Jansen, B. Schumacher, and C. Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), §2, Lemma 2.1, p. 4. The source states the result in the surrounding EDD-ordered setting; this formal statement removes EDD because its proof uses only the nested eligible sets.

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_2_1_without_EDD {m : ℕ} (I : Instance m) (j : Fin I.n) :
    I.p j ≤ a I j ∧ a I j ≤ I.d j + 1 ∧
    cbar I j = Finset.Icc (a I j) (I.d j) ∧
    (cbar I j = ∅ → a I j = I.d j + 1) := by sorry

end LawlerCompress.TardyJobs
