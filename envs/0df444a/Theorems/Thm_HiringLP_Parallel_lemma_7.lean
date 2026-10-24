-- Prove2me | Theorems.Thm_HiringLP_Parallel_lemma_7
-- name    : HiringLP.Parallel.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:07.181166+00:00
-- url     : https://prove2.me/theorems/46c360ac-5209-4c98-bb6e-14b73a45c2b5
-- title:
--   Lemma 7, p. 23 — E(v*_j(D)) ≥ E(v*_j(D̃)): GKPS rounding is no worse than independent rounding
-- statement:
--   Let $I$ be a valid Parallel Offering instance with acceptance decisions $A_i$ ($\mathbb P(j\in A_i)=p_{ij}$, independent across candidates), $y$ a feasible solution of $\mathrm{LP}_{\mathrm{par}}(I)$ and $Y$ a GKPS rounding of $y$, drawn independently of the acceptance decisions. Let $D_j=\{i:Y_{ij}=1,\ j\in A_i\}$, and let $\tilde D_j$ be the random set that contains each candidate $i$ independently with probability $y_{ij}p_{ij}$ (independent Bernoulli $\tilde Y_{ij}$ with mean $y_{ij}$ in place of $Y_{ij}$). Then for every position $j\in[k]$,
--   $$\mathbb E\big(v^*_j(D)\big)\ \ge\ \mathbb E\big(v^*_j(\tilde D)\big).$$
--
--   The dependent rounding thus loses nothing, position by position, against independent rounding with the same marginals.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 23, Lemma 7 (proof App. C.2, p. ec10)

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- Lemma 7 (p. 23): for every position `j`, `E(v*_j(D)) ≥ E(v*_j(D̃))`, where `D_j` comes from the
GKPS rounding `Y ~ μ` of the feasible LP solution `y` and the candidates' acceptance decisions, and
`D̃_j` from independent Bernoulli(`y_ij`) variables in place of `Y`. -/
theorem lemma_7 {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (hacc : AccLaw I acc)
    (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ) (j : Fin k) :
    EvDtilde I y j ≤ EvD I acc μ j := by sorry

end HiringLP.Parallel
