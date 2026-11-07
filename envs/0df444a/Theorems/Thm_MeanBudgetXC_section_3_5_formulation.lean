-- Prove2me | Theorems.Thm_MeanBudgetXC_section_3_5_formulation
-- name    : MeanBudgetXC.section_3_5_formulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:51.764331+00:00
-- url     : https://prove2.me/theorems/068d6f09-c96a-4969-8210-5c722c9a644b
-- title:
--   Section 3.5 — the quadratic formulation projects onto $P_B$ for $0\le B\le 2$
-- statement:
--   Let $3\le d\le N$ and $0\le B\le2$. A pair array $q$ lies in the budgeted body $P_B$ of activity two if and only if the system of Section 3.5 has a solution $(p,\tau,z,u,v,w,\lambda,\mu)$ for this $q$. The first group of the system consists of the star and budget conditions, and the second is the dual certificate of the RLT problem.
--
--   This is the exact linear description behind the upper bound of Theorem 1.1. The range $B\le2$ is what makes the description valid.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: the row $v_{ij}+v_{ji}-w_{ij}+\mu_i+\mu_j\ge-q_{ij}$ for $i<j$ → the same row for every ordered pair; reason: the two orders of one unordered pair give the same inequality, so the solution set is unchanged
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.5, pp.15–16

import Mathlib
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_budgetTwoSystem

namespace MeanBudgetXC

/-- **Section 3.5, the quadratic formulation** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition
for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 3.5,
pp.15–16). For `3 ≤ d ≤ N` and `0 ≤ B ≤ 2`, a pair array `q` lies in the budgeted body `P_B` if and
only if the system of Section 3.5 (first group: star and budget conditions; second group: dual
certificate) has a solution `(p, τ, z, u, v, w, λ, μ)` for this `q`. The system has
`(5M + 3N + 1) + (4M + 2N + 1) = 9M + 5N + 2` inequalities, `6M + 4N + 1` variables and no
equations.

**Formalization Note** The vertex set is a generic finite type `V` with `N = card V`. -/
theorem section_3_5_formulation {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd3 : 3 ≤ d)
    (hdN : d ≤ Fintype.card V) (B : ℝ) (hB0 : 0 ≤ B) (hB2 : B ≤ 2) (q : Pair V → ℝ) :
    q ∈ budgetBody V d 2 B ↔
      ∃ (p τ u mu : V → ℝ) (z v : OPair V → ℝ) (w : Pair V → ℝ) (lam : ℝ),
        budgetTwoSystem d B q p τ u mu z v w lam := by sorry

end MeanBudgetXC
