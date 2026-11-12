-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_theorem_1_1
-- name    : LawlerCompress.TardyJobs.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:49.00821+00:00
-- url     : https://prove2.me/theorems/440a1b3f-0462-45c7-9747-eb83d4f0d559
-- title:
--   Theorem 1.1 — Exact optimum and optimal schedule with compressed resources
-- statement:
--   There exist two fixed finite programs, one returning the optimal late weight and one returning an optimal complete schedule, and a fixed call-depth bound D. For every m≥1 there are positive integer constants C,c depending only on m such that, for every nonempty input instance I in arbitrary job order, writing d=d_max, g=n+d^{m+1} and B=2+m+n+d+Σ_jw_j, the value program terminates within
--
--   $$\lfloor Cg(1+\ln g)\rfloor\ \text{steps using at most }C(n+d^m)\ \text{cells}.$$
--
--   Its result is an attained optimum of the late-weight minimization problem. In the same time bound, the schedule program returns an optimal schedule, using some S cells with
--
--   $$S\le C(n+d^m)+Cd^{m+1}(1+\ln d).$$
--
--   Every job appears exactly once in that schedule. Both runs use word bound B^c and depth bound D; the full schedule output region lies inside S. No EDD assumption is made on the input, and the weights are arbitrary positive integers. This is the complete headline result, combining the optimal value, both resource bounds and optimal schedule reconstruction.
--
--   **Formalization Note** The programs and D precede m; C,c follow m but precede the instance. The schedule is encoded by original input job positions, so sorting cannot change job identities.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - reading: unit-cost algorithm time and space with no explicit machine syntax, word size or call-depth convention → fixed finite Light programs, addition/subtraction/multiplication and memory instructions, polynomial word limit B^c, depth fixed before m; reason: makes all computation charged and keeps local storage uniform; limits are conclusion-side bounds and do not restrict instances
--   - generalization: soft-O time and additional-space bounds → time Cg(1+ln g), extra space Cd^(m+1)(1+ln d), constants uniform before the instance; reason: each envelope has exactly one logarithmic factor, which is one admissible polylogarithmic factor, so it implies the printed soft-O bound; the estimates on pp. 5, 7–8 deliver exactly this single logarithm
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 2, Theorem 1.1; repeated and proved p. 8

import Definitions.Def_LawlerCompress_TardyJobs_Interface

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem theorem_1_1 :
    ∃ Pv Ps : Light.Program, ∃ D : ℕ,
    ∀ m : ℕ, 1 ≤ m → ∃ C c : ℕ, 0 < C ∧ 0 < c ∧
    ∀ I : Instance m, 1 ≤ I.n →
      (∃ S : ℕ, S ≤ baseSpace I C ∧
        Light.Ends (limits I c S D) Pv 0 entry (start I)
          (timeBound I C) (ValueOutput I)) ∧
      (∃ S : ℕ, (S : ℝ) ≤ scheduleSpace I C ∧
        Light.Ends (limits I c S D) Ps 0 entry (start I)
          (timeBound I C) (fun σ =>
            ∃ τ : JobLists I, OutputSchedule I S τ σ ∧ IsOptSchedule I τ)) := by sorry

end LawlerCompress.TardyJobs
