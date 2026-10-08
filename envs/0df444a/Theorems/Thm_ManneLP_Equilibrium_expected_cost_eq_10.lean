-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_expected_cost_eq_10
-- name    : ManneLP.Equilibrium.expected_cost_eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:28.957861+00:00
-- url     : https://prove2.me/theorems/f68b5de9-be1f-49c8-b8a7-75973499a001
-- title:
--   §5, (10) — the expected monthly cost (1) under the joint law xᵢⱼpₙ equals Σcᵢⱼxᵢⱼ
-- statement:
--   Consider Manne's inventory model and assume that, for every admissible pair $(i,j)$, the series $\sum_n p_nC_3(n-i-j)$ converges absolutely. Let $x_{ij}$, $(i,j)\in A$, be any real weights, write $y_i=\sum_jx_{ij}$, and take expectations with respect to the joint law $x_{ij}p_n$ of initial stock, production and demand. Then
--   $$
--   \mathcal EC_1(i)=\sum_i y_iC_1(i)=\sum_{i,j}x_{ij}C_1(i),\qquad
--   \mathcal EC_2(j)=\sum_{i,j}x_{ij}C_2(j),\qquad
--   \mathcal EC_3(n-k)=\sum_{i,j}x_{ij}\sum_np_nC_3(n-i-j),
--   $$
--   and consequently the expected monthly cost (1) equals the linear objective (9),
--   $$
--   \mathcal EC_1(i)+\mathcal EC_2(j)+\mathcal EC_3(n-k)=\sum_{i,j}c_{ij}x_{ij},\qquad c_{ij}=C_1(i)+C_2(j)+\sum_np_nC_3(n-i-j).
--   $$
--
--   This justifies the choice (10) of the cost coefficients: minimizing (9) over the feasible set is minimizing the expected monthly cost.
--
--   **Formalization Note** The expected costs are defined from the joint law $x_{ij}p_n$ as sums over $(i,j,n)$, so the identities use $\sum_np_n=1$ and the independence of demand; they are not definitional. The summability hypothesis states that the expected shortage cost at each admissible pair is finite, which the page takes for granted. The identities are stated for every $x$, not only for probability vectors.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 262 (PDF p. 5), §5, display before (10) and (10); expression (1) on p. 260

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem expected_cost_eq_10 (M : Model)
    (hsum : ∀ a ∈ M.A,
      Summable (fun n : ℕ => M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ))))
    (x : ℕ × ℕ → ℝ) :
    expC₁ M x = ∑ i ∈ states M, marginal M x i * M.C₁ i ∧
      expC₁ M x = ∑ a ∈ M.A, x a * M.C₁ a.1 ∧
      expC₂ M x = ∑ a ∈ M.A, x a * M.C₂ a.2 ∧
      expC₃ M x = ∑ a ∈ M.A, x a * ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)) ∧
      expCost M x = lpObj M x := by sorry

end ManneLP.Equilibrium
