-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_proposition_6
-- name    : OptimalRLS.Minimax.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:32.742182+00:00
-- url     : https://prove2.me/theorems/d5e08057-1326-4aa3-989f-0b9892626105
-- title:
--   Proposition 6, p. 24 — for m > 16, at least e^(m/24) sign vectors in {−1, +1}^m with pairwise Σ(σᵢⁿ − σⱼⁿ)² ≥ m
-- statement:
--   For every integer $m > 16$ there exist $N \in \mathbb N$ and sign vectors $\sigma_1, \dots, \sigma_N \in \{-1, +1\}^m$, $\sigma_i = (\sigma_i^1, \dots, \sigma_i^m)$, such that
--   $$\sum_{n=1}^m (\sigma_i^n - \sigma_j^n)^2 \ge m \quad \text{for all } i \ne j, \qquad\qquad N \ge e^{m/24}.$$
--
--   Since $(\sigma_i^n - \sigma_j^n)^2 \in \{0, 4\}$, the first condition says that any two of the vectors differ in at least $m/4$ coordinates. This is a packing bound for the Hamming cube of Varshamov–Gilbert type; it supplies the exponentially many well-separated hypotheses of Proposition 5.
--
--   **Formalization Note.** The page writes the index condition as "$i \ne, j = 1, \dots N$"; it is read as $i \ne j$, $i, j \in \{1, \dots, N\}$. The vectors are real-valued functions on $\{0, \dots, m-1\}$ taking the values $\pm 1$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 6, p. 24

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-- **Proposition 6**, Caponnetto & De Vito (2007), p. 24. For every integer `m > 16` there are
`N ∈ ℕ` and sign vectors `σ₁, …, σ_N ∈ {−1, +1}^m` with `∑ₙ (σᵢⁿ − σⱼⁿ)² ≥ m` for all `i ≠ j`
and `N ≥ e^{m/24}`. (The page's "i ≠, j = 1, … N" is read as `i ≠ j`.) -/
theorem proposition_6 :
    ∀ m : ℕ, 16 < m → ∃ N : ℕ, ∃ σ : Fin N → Fin m → ℝ,
      (∀ i k, σ i k = 1 ∨ σ i k = -1) ∧
      (∀ i j, i ≠ j → (m : ℝ) ≤ ∑ k, (σ i k - σ j k) ^ 2) ∧
      Real.exp ((m : ℝ) / 24) ≤ N := by sorry

end OptimalRLS.Minimax
