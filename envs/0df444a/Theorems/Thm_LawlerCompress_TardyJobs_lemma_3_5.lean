-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_3_5
-- name    : LawlerCompress.TardyJobs.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:29:29.902327+00:00
-- url     : https://prove2.me/theorems/8e9b8368-5cb8-4329-ab25-48bba4acaabc
-- title:
--   Lemma 3.5 — Sparse reconstruction and attainable on-time weight
-- statement:
--   For every nonempty EDD instance I on m≥1 machines there exists a complete schedule τ with
--
--   $$E_I(\tau)\ge\operatorname{algValue}(I).$$
--
--   There is also a fixed-depth concrete sparse-pointer implementation with constants C,c depending only on m. Starting from the input, its preparation procedure finishes within ⌊Cg(1+ln g)⌋ steps, returns algValue(I), and leaves the completed table, associated pointers and immutable sparse records in the specified memory. From that very state its extraction procedure returns a complete schedule with at least that on-time weight in at most
--
--   $$C(n+d_{\max}^m)\quad\text{additional steps}.$$
--
--   Both phases share a word limit B^c and some cell limit S≤C(n+d_max^m)+Cd_max^{m+1}(1+ln d_max), where g=n+d_max^{m+1} and B=2+m+n+d_max+Σ_jw_j. Extraction preserves every allocated record, and the output’s entire 2n-cell region lies within S. This retains both the existence and constructive clauses, including the extraction bound without a logarithmic factor.
--
--   **Formalization Note** Preparation and extraction are procedures zero and one of the same fixed program. The pure schedule clause and the execution clause form one target.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - reading: unit-cost algorithm time and space with no explicit machine syntax, word size or call-depth convention → fixed finite Light programs, addition/subtraction/multiplication and memory instructions, polynomial word limit B^c, depth fixed before m; reason: makes all computation charged and keeps local storage uniform; limits are conclusion-side bounds and do not restrict instances
--   - generalization: soft-O time and additional-space bounds → time Cg(1+ln g), extra space Cd^(m+1)(1+ln d), constants uniform before the instance; reason: each envelope has exactly one logarithmic factor, which is one admissible polylogarithmic factor, so it implies the printed soft-O bound; the estimates on pp. 5, 7–8 deliver exactly this single logarithm
--   - encoding: back links recorded before batch writes and followed after the dynamic program → nested executions through the same state with BacklinkReady and preservation of the allocated record region; reason: specifies the completed table, every associated pointer and the sparse immutable records explicitly; equality retains the earlier candidate
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 8, Lemma 3.5

import Definitions.Def_LawlerCompress_TardyJobs_Backlinks

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_3_5 :
    ∃ D : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ C c : ℕ, 0 < C ∧ 0 < c ∧
    ∀ I : Instance m, 1 ≤ I.n → EDD I →
      (∃ τ : JobLists I, Schedule I τ ∧ algValue I ≤ onTimeWeight I τ) ∧
      ∃ S : ℕ, (S : ℝ) ≤ scheduleSpace I C ∧
        Light.Ends (limits I c S D) algorithm2BacklinkProgram 0 entry (start I)
          (timeBound I C) (fun σ₁ =>
            BacklinkReady I S σ₁ ∧ σ₁.loc 0 = (algValue I : ℤ) ∧
            Light.Ends (limits I c S D) algorithm2BacklinkProgram 0 (.call 1 [] 0) σ₁
              (C * (I.n + dmax I ^ m)) (fun σ₂ =>
                RecordsPreserved I σ₁ σ₂ ∧
                ∃ τ : JobLists I, Schedule I τ ∧ OutputSchedule I S τ σ₂ ∧
                  algValue I ≤ onTimeWeight I τ)) := by sorry

end LawlerCompress.TardyJobs
