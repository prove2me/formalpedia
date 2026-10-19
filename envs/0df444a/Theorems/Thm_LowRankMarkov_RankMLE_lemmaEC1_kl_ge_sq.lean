-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_lemmaEC1_kl_ge_sq
-- name    : LowRankMarkov.RankMLE.lemmaEC1_kl_ge_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:10.243487+00:00
-- url     : https://prove2.me/theorems/027ad4dd-56cf-4bc5-a6b4-a85025fa5ff4
-- title:
--   Lemma EC.1 (first display), ec1 — D_KL(u, v) ≥ {pα/(2β²)}‖u − v‖₂² for u_j ∈ {0} ∪ [α/p, β/p], v_j ∈ [α/p, β/p]
-- statement:
--   Let $p\ge1$ and $\alpha,\beta>0$. Let $u,v\in\mathbb R^p$ be discrete distributions, $\sum_ju_j=\sum_jv_j=1$, such that for every $j\in[p]$
--   $$u_j\in\{0\}\cup[\alpha/p,\beta/p],\qquad v_j\in[\alpha/p,\beta/p].$$
--   Then
--   $$D_{\mathrm{KL}}(u,v)=\sum_{j:\,u_j\neq0}u_j\log\frac{u_j}{v_j}\ \ge\ \frac{p\alpha}{2\beta^2}\,\|u-v\|_2^2 .$$
--
--   This reverse-Pinsker inequality converts KL-divergence bounds into squared $\ell_2$ bounds row by row, and is how the paper passes between its KL and Frobenius-norm error bounds.
--
--   **Formalization Note** Nonnegativity of $u$ follows from the range condition, so "discrete distribution" is encoded by the range conditions and the unit sums.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec1 (PDF p. 34), Lemma EC.1, first display

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- Lemma EC.1, first display, ec1, arXiv:1907.00113v2: for discrete distributions `u, v` on `[p]`
with `u_j ∈ {0} ∪ [α/p, β/p]` and `v_j ∈ [α/p, β/p]`,
`D_KL(u, v) ≥ {pα/(2β²)} ‖u − v‖₂²`. -/
theorem lemmaEC1_kl_ge_sq {p : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (u v : Fin p → ℝ) (hu_sum : ∑ j, u j = 1) (hv_sum : ∑ j, v j = 1)
    (hu : ∀ j, u j = 0 ∨ (α / (p : ℝ) ≤ u j ∧ u j ≤ β / (p : ℝ)))
    (hv : ∀ j, α / (p : ℝ) ≤ v j ∧ v j ≤ β / (p : ℝ)) :
    (p : ℝ) * α / (2 * β ^ 2) * ∑ j, (u j - v j) ^ 2 ≤ klVec u v := by sorry

end LowRankMarkov.RankMLE
