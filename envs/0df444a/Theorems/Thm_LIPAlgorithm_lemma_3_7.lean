-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_3_7
-- name    : LIPAlgorithm.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:20.951549+00:00
-- url     : https://prove2.me/theorems/295cb081-e7c1-4fe4-acd9-3a41a0c620b8
-- title:
--   Lemma 3.7 — residual rank bound
-- statement:
--   Let $L$ be a rank-$n$ well-rounded lattice and $w\in\mathbb R^n$. With $\mathrm{Amb}(w)$, $J(w)$ and the fixed vectors $u_j(w)=p_j(w)-p_{j-1}(w)$ as defined:
--
--   1. for $j\in J(w)$, the sets representing the vertices satisfy $B_j=B_{j-1}\cup\{u_j(w)\}$;
--   2. the $u_j(w)$, $j\in J(w)$, lie in $A=\mathrm{Min}(L)$ and are linearly independent;
--   3. $$|J(w)|\ge n-2\,\mathrm{Amb}(w),$$
--   so the number of steps left unfixed is at most $2\,\mathrm{Amb}(w)$.
--
--   Few ambiguous ranks thus fix a large sublattice.
--
--   Differences from the source:
--   - generalization: w ∈ L* → every w ∈ ℝⁿ; reason: the proof does not use w ∈ L*, and L* ⊂ ℝⁿ
--   - generalization: the conclusion of the lemma → the conclusion, plus the clause B_j = B_{j−1} ∪ {u_j(w)}; reason: the printed proof derives this clause, and later sections use it; the source's claim is a sub-conjunction
--   - encoding: |J(w)| ≥ n − 2Amb(w) → n ≤ |J(w)| + 2·Amb(w); reason: the same inequality without natural subtraction
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 3.7, p.20

import Mathlib
import Definitions.Def_LIPAlgorithm_Resolved

namespace LIPAlgorithm

/-- **Lemma 3.7 (Residual rank bound).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…),
Lemma 3.7, p.20 (PDF p.23). The fixed vectors `u_j(w)`, `j ∈ J(w)`, are linearly independent vectors of `A = Min(L)`, and
`|J(w)| ≥ n − 2·Amb(w)`, written without subtraction.

The first clause is the nesting that the printed proof derives: for `j ∈ J(w)`, the sets `B_j`, `B_{j−1}` that represent
the vertices satisfy `B_j = B_{j−1} ∪ {u_j(w)}`.

**Formalization Note.** `w` ranges over `ℝⁿ`, which contains `L*`. -/
theorem lemma_3_7 {n : ℕ} (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : IsWellRounded L) (w : E n) :
    (∀ j ∈ fixedSteps L w, ∃ B ∈ indepSets L j, ∃ B' ∈ indepSets L (j - 1),
      pSum B = vertexAt L j w ∧ pSum B' = vertexAt L (j - 1) w ∧
        (B : Set (E n)) = insert (fixedVec L j w) (B' : Set (E n))) ∧
    (∀ j ∈ fixedSteps L w, fixedVec L j w ∈ minShell L) ∧
    LinearIndependent ℝ (fun j : fixedSteps L w => fixedVec L (j : ℕ) w) ∧
    n ≤ (fixedSteps L w).card + 2 * ambCount L w := by sorry

end LIPAlgorithm
