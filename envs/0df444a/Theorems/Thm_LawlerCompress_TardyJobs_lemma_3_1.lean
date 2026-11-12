-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_3_1
-- name    : LawlerCompress.TardyJobs.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:12.968901+00:00
-- url     : https://prove2.me/theorems/56a9d70b-5068-4fb0-b440-fb53a9307cbf
-- title:
--   Lemma 3.1 — The reverse heap computes the canonical endpoints
-- statement:
--   For a nonempty EDD instance I on m≥1 machines, let a′_j be the output of the reverse-index heap procedure of §3.1 and a_j the least canonical completion time with default d_j+1. Then
--
--   $$\forall j\in\{1,\ldots,n\},\qquad a'_j=a_j.$$
--
--   This identifies the procedurally obtained interval endpoints with the canonical sets, including empty intervals and ties.
--
--   **Formalization Note** The finite-set fold specifies the heap contents, with an evicted job assigned the inserted job’s due date plus one; execution costs belong to Lemma 3.2.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 6, Lemma 3.1

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_3_1 {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∀ j : Fin I.n, heapEndpoints I j = a I j := by sorry

end LawlerCompress.TardyJobs
