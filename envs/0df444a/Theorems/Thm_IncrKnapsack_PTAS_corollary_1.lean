-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_corollary_1
-- name    : IncrKnapsack.PTAS.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:13.36366+00:00
-- url     : https://prove2.me/theorems/ee11a5b1-ddb5-42f0-b965-9f1126813bda
-- title:
--   Corollary 1, p. 23 — F(M, L, ϕ_M) < ∞ for every ϕ_M ≤ (1 − 2ε)·Ψ(S*)
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, and let $\epsilon = 1/K$ with $K > 4$ an integer. Work with the rounded profits of §2.2, and let $\mathcal S^*$ be an optimal solution for them. Let $\xi \in \{0, \dots, K-1\}$ be a shift with $\Psi(\mathcal S_\xi) \ge (1-\epsilon)\cdot\Psi(\mathcal S^*)$; such a shift exists by Lemma 7. Let $M$ be the number of clusters and $L$ the largest profit class index for this shift. Then the exact cluster program satisfies
--
--   $$F(M, L, \varphi_M) < \infty \qquad\text{for every } \varphi_M \le (1-2\epsilon)\cdot\Psi(\mathcal S^*).$$
--
--   In words: some feasible uncrossing-stars solution that uses good periods only reaches profit $(1-2\epsilon)\Psi(\mathcal S^*)$. Together with Claim 3 this places a large grid value in the reach of the approximate program.
--
--   **Formalization Note.** $F$ is evaluated with the shifted class bound `Lmax + 1`, i.e. classes $\mathcal P_0, \dots, \mathcal P_L$. Profits of uncrossing-stars solutions are sums of item contributions with the full-horizon $\lambda^{t+}$.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 23, §3.4, Corollary 1

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem corollary_1 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Sstar : Sol I) (hopt : IsOptimal I (pr I K) Sstar)
    (hshift : (1 - eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (restrictGood I K ξ Sstar)) :
    ∀ ϕ : ℝ, ϕ ≤ (1 - 2 * eps K) * Psi I (pr I K) Sstar →
      F I K ξ (Mcl I K ξ) (Lmax I K + 1) ϕ < ⊤ := by sorry
end IncrKnapsack.PTAS
