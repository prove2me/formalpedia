-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_fact1_stick_breaking
-- name    : OptimisticPSRL.Concentration.fact1_stick_breaking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:41.809693+00:00
-- url     : https://prove2.me/theorems/5e8fae06-fa30-4a78-ab05-5f3d34f9a7d2
-- title:
--   Fact 1, p. 17 — stick-breaking identity for (p̃ − p̄)ᵀh
-- statement:
--   Fix the order $1,\dots,S$ of the states, let $\tilde p,\bar p\in\Delta^S$ be probability vectors and set
--
--   $$
--   \tilde y_i=\frac{\tilde p_i}{\tilde p_i+\cdots+\tilde p_S},\quad \bar y_i=\frac{\bar p_i}{\bar p_i+\cdots+\bar p_S},\quad \tilde H_{i+1}=\frac{\sum_{j=i+1}^S h_j\tilde p_j}{\sum_{j=i+1}^S\tilde p_j},\quad \bar H_{i+1}=\frac{\sum_{j=i+1}^S h_j\bar p_j}{\sum_{j=i+1}^S\bar p_j}.
--   $$
--
--   Then for every $h\in\mathbb R^S$,
--
--   $$
--   (\tilde p-\bar p)^Th=\sum_i(\tilde y_i-\bar y_i)(h_i-\tilde H_{i+1})(\bar p_i+\cdots+\bar p_S)=\sum_i(\tilde y_i-\bar y_i)(h_i-\bar H_{i+1})(\tilde p_i+\cdots+\tilde p_S).
--   $$
--
--   The identity rewrites a difference of two distributions along a direction $h$ in terms of the differences of their stick-breaking ratios. Agrawal and Jia use it both for Dirichlet samples (Proposition 5.1) and, with $\tilde p=\hat p$ and $\bar p=p$, for empirical vectors (Proposition 5.2).
--
--   **Formalization Note** The order is the natural order of `Fin S`; since the states are arbitrary labels, this covers every ordering. Ratios with a vanishing denominator are $0$. Both equalities are stated, as a conjunction.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 17, Fact 1

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

namespace OptimisticPSRL.Concentration

/-- **Fact 1** (Agrawal–Jia, arXiv:1705.07041v3, p. 17), for the natural order of `Fin S`:
for probability vectors `p̃ = pt`, `p̄ = pb` and any `h`,
`(p̃ − p̄)ᵀh = ∑_i (ỹ_i − ȳ_i)(h_i − H̃_{i+1})(p̄_i + ⋯ + p̄_S)
           = ∑_i (ỹ_i − ȳ_i)(h_i − H̄_{i+1})(p̃_i + ⋯ + p̃_S)`. -/
theorem fact1_stick_breaking {S : ℕ} (pt pb h : Fin S → ℝ) (hpt : IsProbVec pt)
    (hpb : IsProbVec pb) :
    (∑ i, (pt i - pb i) * h i =
        ∑ i, (yRatio pt i - yRatio pb i) * (h i - Hnext pt h i) * tail pb i) ∧
      (∑ i, (pt i - pb i) * h i =
        ∑ i, (yRatio pt i - yRatio pb i) * (h i - Hnext pb h i) * tail pt i) := by sorry

end OptimisticPSRL.Concentration
