-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_3_4
-- name    : LawlerCompress.TardyJobs.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:09.922216+00:00
-- url     : https://prove2.me/theorems/f715d673-12ff-415a-abd9-2f9b3ffea00c
-- title:
--   Lemma 3.4 — Concrete Algorithm 2 time and space
-- statement:
--   The fixed concrete Algorithm 2 program has a call-depth bound D independent of m. For each m≥1 there exist positive integer constants C,c chosen before the instance such that, for every nonempty EDD instance I, it terminates and returns exactly the recurrence value w=algValue(I), using some S cells with
--
--   $$S\le C(n+d_{\max}^{m}),\qquad T\le\lfloor Cg(1+\ln g)\rfloor,\qquad W\le B^c,\quad g=n+d_{\max}^{m+1}.$$
--
--   Here B=2+m+n+d_max+Σ_jw_j. This resource assertion is about the particular finite syntax implementing the printed algorithm, including interval preprocessing, table initialization, tuple enumeration, deferred writes and the final scan.
--
--   **Formalization Note** The program is fixed in the definition layer, before D,m,C,c and the input; no output-only existential program replaces it.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - reading: unit-cost algorithm time and space with no explicit machine syntax, word size or call-depth convention → fixed finite Light programs, addition/subtraction/multiplication and memory instructions, polynomial word limit B^c, depth fixed before m; reason: makes all computation charged and keeps local storage uniform; limits are conclusion-side bounds and do not restrict instances
--   - generalization: Õ_m(n+d_max^(m+1)) time and O_m(n+d_max^m) space for Algorithm 2 → the concrete program returns algValue under explicit Cg(1+ln g) time and C(n+d^m) cell bounds; reason: Cg(1+ln g) has one admissible polylogarithmic factor, so it implies the printed Õ_m time bound (C(n+d^m) is the printed O_m space bound); the proof on p. 7 with Lemma 2.3 delivers exactly this single logarithm, and the return identity identifies the printed algorithm
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 7, Lemma 3.4

import Definitions.Def_LawlerCompress_TardyJobs_Programs

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_3_4 :
    ∃ D : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ C c : ℕ, 0 < C ∧ 0 < c ∧
    ∀ I : Instance m, 1 ≤ I.n → EDD I →
      ∃ S : ℕ, S ≤ baseSpace I C ∧
        Light.Ends (limits I c S D) algorithm2Program 0 entry (start I)
          (timeBound I C) (fun σ => σ.loc 0 = (algValue I : ℤ)) := by sorry

end LawlerCompress.TardyJobs
