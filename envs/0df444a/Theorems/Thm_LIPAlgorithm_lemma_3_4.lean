-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_3_4
-- name    : LIPAlgorithm.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:22.445929+00:00
-- url     : https://prove2.me/theorems/c6d0c1da-2045-48a4-b337-47fc1afa7799
-- title:
--   Lemma 3.4 — projected vertices are uniquely represented
-- statement:
--   Let $L$ be a rank-$n$ well-rounded lattice, $A=\mathrm{Min}(L)$, and $1\le j\le n$. If $p$ is a vertex of $P_j$, there is a unique independent set $B\subseteq A$ of size $j$ with
--
--   $$p=p_B=\sum_{b\in B}b.$$
--
--   This identifies the vertex of a resolved rank with a set of shortest vectors.
--
--   Differences from the source:
--   - encoding: a vertex of P_j → an extreme point of P_j; reason: the paper's definition of vertex, p.17: not a nontrivial convex combination of other points
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 3.4, p.18

import Mathlib
import Definitions.Def_LIPAlgorithm_Resolved

namespace LIPAlgorithm

/-- **Lemma 3.4 (Projected vertices are uniquely represented).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission
(manuscript sha256 61ee52aa…), Lemma 3.4, p.18 (PDF p.21). `L` is a rank-`n` well-rounded lattice (§3 preamble, p.17). A vertex
`p` of `P_j` has a unique independent `j`-set `B ⊆ Min(L)` with `p = p_B`. -/
theorem lemma_3_4 {n : ℕ} (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : IsWellRounded L) (j : ℕ) (hj₁ : 1 ≤ j) (hj₂ : j ≤ n) (p : E n)
    (hp : p ∈ (polyP L j).extremePoints ℝ) :
    ∃! B : Finset (E n), B ∈ indepSets L j ∧ pSum B = p := by sorry

end LIPAlgorithm
