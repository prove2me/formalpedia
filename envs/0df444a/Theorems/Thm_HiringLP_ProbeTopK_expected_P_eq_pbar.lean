-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_expected_P_eq_pbar
-- name    : HiringLP.ProbeTopK.expected_P_eq_pbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:19.666083+00:00
-- url     : https://prove2.me/theorems/58aaf31c-af65-402c-896d-eed067d81422
-- title:
--   §4.4, p. 18 — the cut indicator has mean E(P_i) = Σ_j q_ij · x_ij/(q_ij y_i) = p_i
-- statement:
--   Let $(x, y)$ be a feasible solution of $\mathrm{LP}_{ptk}(I)$ and $i \in [n]$. Let $P_i$ be the indicator that applicant $i$, if interviewed while positions remain, would be hired: given $V_i = r_j$, $P_i = 1$ with probability $x_{ij}/(y_i q_{ij})$. Then
--
--   $$
--   \mathbb{E}(P_i) = \sum_{j=1}^J q_{ij}\,\frac{x_{ij}}{y_i q_{ij}} = p_i = \frac{\sum_j x_{ij}}{y_i},
--   $$
--
--   with the conventions that $x_{ij}/(y_i q_{ij}) = 0$ when $y_i q_{ij} = 0$ and $p_i = 0$ when $y_i = 0$.
--
--   This identifies the probability that applicant $i$ "makes the cut" with the LP quantity $p_i$ of (4), which turns the algorithm's reward into a function of $(p_i, v_i, y_i)$ only.
--
--   **Formalization Note.** Feasibility forces $x_{ij} = 0$ whenever $y_i q_{ij} = 0$, so the zero conventions are consistent with the page's computation.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 18, §4.4, first display

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem expected_P_eq_pbar {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) (i : Fin n) :
    ∑ j, I.q i j * coin I x y i j = pbar x y i := by sorry

end HiringLP.ProbeTopK
