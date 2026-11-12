-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_3_2
-- name    : LawlerCompress.TardyJobs.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:32.555195+00:00
-- url     : https://prove2.me/theorems/1aedcad8-09ba-48ab-a4b2-b4f1ffcce82a
-- title:
--   Lemma 3.2 — Endpoint computation in O(n log n) time and O(n) space
-- statement:
--   There exist one finite program P, a fixed call-depth bound D and positive integer constants C,c, all chosen before the number of machines, such that for every m≥1 and every nonempty EDD instance I, P returns all canonical endpoints a₁,…,a_n. It uses some number S of addressed cells satisfying
--
--   $$S\le Cn,\qquad T\le\lfloor Cn(1+\ln n)\rfloor,\qquad W\le B^c,\qquad B=2+m+n+d_{\max}+\sum_jw_j.$$
--
--   The returned nonnegative address points to the n endpoint cells, and their entire region lies below S. In particular, the constants do not depend on m, and no term involving d_max occurs in the time or space bounds. This is the preprocessing resource target.
--
--   **Formalization Note** Light.Ends requires actual terminating execution within the stated step, cell, word and depth limits.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - reading: unit-cost algorithm time and space with no explicit machine syntax, word size or call-depth convention → fixed finite Light programs, addition/subtraction/multiplication and memory instructions, polynomial word limit B^c, depth fixed before m; reason: makes all computation charged and keeps local storage uniform; limits are conclusion-side bounds and do not restrict instances
--   - encoding: O(n log n) including a singleton input → Cn(1+ln n) with positive C; reason: the explicit envelope is positive at n=1 and has the printed asymptotic order
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 6, Lemma 3.2

import Definitions.Def_LawlerCompress_TardyJobs_Interface

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_3_2 :
    ∃ P : Light.Program, ∃ D C c : ℕ, 0 < C ∧ 0 < c ∧
    ∀ m : ℕ, 1 ≤ m → ∀ I : Instance m, 1 ≤ I.n → EDD I →
      ∃ S : ℕ, S ≤ C * I.n ∧
        Light.Ends (limits I c S D) P 0 entry (start I)
          ⌊(C : ℝ) * I.n * (1 + Real.log I.n)⌋₊ (EndpointOutput I S) := by sorry

end LawlerCompress.TardyJobs
