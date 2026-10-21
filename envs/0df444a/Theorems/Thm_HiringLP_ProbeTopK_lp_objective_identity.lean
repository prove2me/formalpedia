-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_lp_objective_identity
-- name    : HiringLP.ProbeTopK.lp_objective_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:35.063052+00:00
-- url     : https://prove2.me/theorems/a5400da4-c413-44f6-8657-8cd4c366a507
-- title:
--   App. B.5, p. ec8 — the LPptk objective equals Σ_i y_i v_i p_i
-- statement:
--   Let $(x, y)$ be a feasible solution of $\mathrm{LP}_{ptk}(I)$, and let $p_i, v_i$ be defined by (4) with footnote 2's convention (value $0$ when a denominator vanishes). Then
--
--   $$
--   \sum_{i=1}^n \sum_{j=1}^J r_j x_{ij} \;=\; \sum_{i=1}^n y_i\, \frac{\sum_j r_j x_{ij}}{\sum_j x_{ij}}\, \frac{\sum_j x_{ij}}{y_i} \;=\; \sum_{i=1}^n y_i v_i p_i .
--   $$
--
--   This writes the LP objective as the expectation of the weighted rank function $v^*$ under a distribution whose marginals are $y_i p_i$, which is what lets the correlation gap compare it with the algorithm.
--
--   **Formalization Note.** The page writes $r_{ij}$ for the support value $r_j$ (a typo; the objective of $\mathrm{LP}_{ptk}$ is $\sum r_j x_{ij}$). The terms with a vanishing denominator are $0$ on both sides, because feasibility forces $x_{i\cdot} = 0$ when $y_i = 0$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec8 (PDF p. 40), App. B.5, second display

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem lp_objective_identity {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) :
    LPobj I x y = ∑ i, y i * vbar I x i * pbar x y i := by sorry

end HiringLP.ProbeTopK
