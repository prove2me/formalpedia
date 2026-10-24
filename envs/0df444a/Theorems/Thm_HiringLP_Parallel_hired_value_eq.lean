-- Prove2me | Theorems.Thm_HiringLP_Parallel_hired_value_eq
-- name    : HiringLP.Parallel.hired_value_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:05.311466+00:00
-- url     : https://prove2.me/theorems/c3bebc34-f8cd-457c-b7ee-83f0c4d574c9
-- title:
--   §5.3, p. 23 — the expected value hired for position j equals L_j = E(v*_j(D))
-- statement:
--   Let $I$ be a valid Parallel Offering instance, $y$ a feasible solution of $\mathrm{LP}_{\mathrm{par}}(I)$, $\mu$ a GKPS rounding of $y$, and suppose each list is run in decreasing order of $v_{ij}$. Fix the candidates' acceptance laws arbitrarily. For a position $j$, let $L_j$ be the expected value of the candidate that $\mathrm{ALG}_{\mathrm{par}}$ hires for $j$ (zero if nobody is hired), and let $D_j=\{i: Y_{ij}=1,\ j\in A_i\}$ be the set of candidates on list $j$ who would accept $j$. Then
--   $$L_j=\mathbb E\big(v^*_j(D)\big),\qquad v^*_j(S)=\max_{i\in S}v_{ij},\ v^*_j(\emptyset)=0.$$
--
--   This reduces the analysis of the algorithm to one position at a time and to a function of the random set $D_j$ alone.
--
--   **Formalization Note** $L_j$ is computed from the run of the list (the first accepting candidate in list order, reached within $T$ rounds); the identity holds for every acceptance law, since it holds for every rounded matrix in the support of $\mu$ and every acceptance profile.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 23, §5.3, first paragraph

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- §5.3, p. 23: the expected value `L_j` of the candidate that `ALG_par` hires for position `j`
equals `E(v*_j(D))`, the expected largest value `v_ij` over the set `D_j` of candidates that are on
list `j` and would accept position `j`. Here `y` is feasible for `LP_par(I)`, `μ` has the GKPS
properties (P1)–(P3) with weights `y`, and every list is run in decreasing order of `v_ij`. -/
theorem hired_value_eq {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (ord : Fin k → Equiv.Perm (Fin n)) (hord : IsValueOrder I ord) (j : Fin k) :
    Lpos I acc μ ord j = EvD I acc μ j := by sorry

end HiringLP.Parallel
