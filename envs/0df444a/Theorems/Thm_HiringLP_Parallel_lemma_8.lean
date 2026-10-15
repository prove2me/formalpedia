-- Prove2me | Theorems.Thm_HiringLP_Parallel_lemma_8
-- name    : HiringLP.Parallel.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:04.242987+00:00
-- url     : https://prove2.me/theorems/2cc7b90b-7d76-4038-801f-2b22c0b86534
-- title:
--   Lemma 8, p. 24 — E(v*_j(D̃)) ≥ (1 − 1/e) L*_j
-- statement:
--   Let $I$ be a valid Parallel Offering instance and $y$ a feasible solution of $\mathrm{LP}_{\mathrm{par}}(I)$. For a position $j$, let $\tilde D_j$ contain each candidate $i$ independently with probability $y_{ij}p_{ij}$, and let $L^*_j=\sum_{i=1}^n v_{ij}y_{ij}p_{ij}$. Then
--   $$\mathbb E\big(v^*_j(\tilde D)\big)\ \ge\ \Big(1-\frac1e\Big)L^*_j.$$
--
--   Summed over the positions, the right-hand side is $(1-1/e)$ times the LP objective; together with Lemma 7 this gives the guarantee of $\mathrm{ALG}_{\mathrm{par}}$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 24, Lemma 8 (L*_j defined on p. 23; proof App. C.4, pp. ec11–ec12)

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- Lemma 8 (p. 24): for every position `j` and every feasible solution `y` of `LP_par(I)`,
`E(v*_j(D̃)) ≥ (1 − 1/e) L*_j` with `L*_j = Σ_i v_ij y_ij p_ij`. -/
theorem lemma_8 {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y) (j : Fin k) :
    (1 - Real.exp (-1)) * Lstar I y j ≤ EvDtilde I y j := by sorry

end HiringLP.Parallel
