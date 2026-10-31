-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_lemma_11
-- name    : IncrKnapsack.PTAS.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:21.981641+00:00
-- url     : https://prove2.me/theorems/017291a4-48e1-4239-86f8-e1fb9ce37e20
-- title:
--   Lemma 11, p. 28 — for a good shift ξ the glued solution satisfies Ψ(S̄) ≥ (1 − 7ε)·Ψ(S*)
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, and work with the rounded profits of §2.2. Let $\mathcal S^*$ be an optimal solution, and let $\xi \in \{0,\dots,K-1\}$ be a shift with $\Psi(\mathcal S_\xi) \ge (1-\epsilon)\Psi(\mathcal S^*)$; such a shift exists by Lemma 7. Let $\Phi$ be a profit grid, and let $\mathcal A$ be a single-cluster subroutine with the guarantee of Theorem 3. Let $\bar{\mathcal S}$ be the solution glued along any traceback of the approximate program $\tilde F$ from $(M, L, \tilde\varphi_M)$. Then
--
--   $$\Psi(\bar{\mathcal S}) \ge (1-7\epsilon)\cdot\Psi(\mathcal S^*).$$
--
--   Together with Lemma 10 (feasibility), this is the approximation guarantee of the algorithm on the rounded instance, the core of Theorem 1.
--
--   **Formalization Note.** The last step of the paper's proof uses $\lambda_T p_{\max} \le \Psi(\mathcal S^*)$, "since an objective value of $\lambda_T p_{\max}$ can trivially be attained". This needs the most profitable item to fit into $W_T$, which is the added standing assumption `fits`. The grid hypothesis replaces the printed grid (7). With (7) the lemma is false: with $\epsilon = 1/10$, one period and 20 unit items, even an exact subroutine yields at most 3 items, while $(1-7\epsilon)\Psi(\mathcal S^*) = 6$.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 28–29, §3.6, Lemma 11

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem lemma_11 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Sstar : Sol I) (hopt : IsOptimal I (pr I K) Sstar)
    (hshift : (1 - eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (restrictGood I K ξ Sstar))
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    (1 - 7 * eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (algOut I K ξ Φ A jt ϕt) := by sorry
end IncrKnapsack.PTAS
