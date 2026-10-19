-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_lemmaEC1_frob_le_kl
-- name    : LowRankMarkov.RankMLE.lemmaEC1_frob_le_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:18.313666+00:00
-- url     : https://prove2.me/theorems/24e8dad2-76ac-4dd6-bfae-633528d04331
-- title:
--   Lemma EC.1 (second display), ec1 — ‖P − Q‖_F² ≤ (2β²/(απ_min p)) D_KL(P, Q) under Assumption 1
-- statement:
--   Let $\alpha,\beta>0$ and let $P\in\mathbb R^{p\times p}$ be a primitive transition matrix satisfying Assumption 1 (rank $r$, and $P_{jk}\in\{0\}\cup[\alpha/p,\beta/p]$ for all $j,k$). Let $\pi$ be its stationary probability vector with $\pi_i>0$ for all $i$, and $\pi_{\min}=\min_i\pi_i$. Then for every $Q\in\mathcal C$, the class of row-stochastic matrices in the entrywise box satisfying $\|Q-P\|_*\le4\sqrt2\|Q-P\|_F$,
--   $$\|P-Q\|_F^2\ \le\ \frac{2\beta^2}{\alpha\pi_{\min}p}\,D_{\mathrm{KL}}(P,Q),$$
--   where $D_{\mathrm{KL}}(P,Q)=\sum_{i,j}\pi_iP_{ij}\log(P_{ij}/Q_{ij})1_{\{P_{ij}\ne0\}}$.
--
--   This is the matrix form of Lemma EC.1; it turns a KL bound on an estimator into a Frobenius-norm bound, and it is the step behind the nuclear-norm diameter bound (EC.14).
--
--   **Formalization Note** The section assumes an ergodic chain and a stationary distribution. The cone condition is included as printed, though the rowwise proof does not use it. $\|P-Q\|_F^2$ is written as the sum of squared entries.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec1 (PDF p. 34), Lemma EC.1, second display; Assumption 1, p. 8; set C, p. 14

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- Lemma EC.1, second display, ec1, arXiv:1907.00113v2: under Assumption 1, for every
`Q ∈ 𝒞`, `‖P − Q‖_F² ≤ (2β²/(απ_min p)) D_KL(P, Q)`. -/
theorem lemmaEC1_frob_le_kl {p r : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P Q : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (hQ : ConcentrationClass α β P Q) :
    ∑ i, ∑ j, (P i j - Q i j) ^ 2 ≤ 2 * β ^ 2 / (α * piMin π * p) * klDiv π P Q := by sorry

end LowRankMarkov.RankMLE
