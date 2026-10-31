-- Prove2me | Theorems.Thm_LegalAssign_theorem_2_1
-- name    : LegalAssign.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:27.134634+00:00
-- url     : https://prove2.me/theorems/db60f5ca-4b0d-4080-814e-03f72f27e164
-- title:
--   Theorem 2.1 — Gale–Shapley terminates and outputs the student-optimal (resp. school-optimal) stable assignment
-- statement:
--   Let $(G,<,q)$ be an instance of the stable assignment problem. Every execution of student-proposing Gale–Shapley terminates, and its output $M_0$ is stable with
--   $$M_0(a)\ge_a M'(a)\qquad\text{for every } a\in A \text{ and every stable assignment } M'.$$
--   Every execution of school-proposing Gale–Shapley terminates, and its output $M_z$ is stable with
--   $$M'(a)\ge_a M_z(a)\qquad\text{for every } a\in A \text{ and every stable assignment } M'.$$
--
--   This is the classical existence result for one-to-many instances with quotas, in the form that also gives both extreme stable assignments.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - reading: Gale-Shapley’s algorithm (cited, not stated) "outputs" an assignment → the proposal step relations of Def_LegalAssign_GaleShapley with an arbitrary proposer; every execution terminates (Acc of the reversed step relation at the initial state), an output exists, and every output is optimal; reason: the source never states the procedure; quantifying over all executions matches its "some (equivalently, any) execution" in the proof of Lemma A.6
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Theorem 2.1, p.6

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_GaleShapley

namespace LegalAssign

/-- Theorem 2.1 (arXiv:1809.08506v2, p.6, cited from Gale and Shapley [15]): every execution of
student-proposing (resp. school-proposing) Gale–Shapley terminates, there is an output, and every
output is the student-optimal (resp. school-optimal) stable assignment.

**Formalization Note** `Acc` of the reversed step relation at the initial state says that no
execution is infinite. `IsStudentOptimal M` is "`M` is stable and `M(a) ≥_a M'(a)` for every `a`
and every stable `M'`"; `IsSchoolOptimal M` is the same with `M'(a) ≥_a M(a)`. -/
theorem theorem_2_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    (Acc (fun s' s => G.StudentStep s s') (GSState.init A B) ∧
      (∃ M, Instance.IsGSOutput G.StudentStep M) ∧
      ∀ M, Instance.IsGSOutput G.StudentStep M → G.IsStudentOptimal M) ∧
    (Acc (fun s' s => G.SchoolStep s s') (GSState.init A B) ∧
      (∃ M, Instance.IsGSOutput G.SchoolStep M) ∧
      ∀ M, Instance.IsGSOutput G.SchoolStep M → G.IsSchoolOptimal M) := by sorry

end LegalAssign
