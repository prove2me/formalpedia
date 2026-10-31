-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_filtering
-- name    : IncrKnapsack.PTAS.filtering
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:11.684838+00:00
-- url     : https://prove2.me/theorems/c5774461-2cbf-4bb3-aa3b-e1c52c164a04
-- title:
--   §3.3, p. 21 — removing items with Ψ_i(Ŝ) ≤ (ε/n)·Ψ(Ŝ) keeps a feasible good-period solution with Ψ(S̃) ≥ (1 − ε)·Ψ(Ŝ)
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, and let $\xi \in \{0, \dots, K-1\}$. Work with the rounded profits of §2.2. Let $\hat{\mathcal S}$ be a feasible solution that introduces items only in periods of good intervals. Let $\tilde{\mathcal S}$ be obtained from $\hat{\mathcal S}$ by eliminating every item $i \in \hat S_T$ with
--
--   $$\Psi_i(\hat{\mathcal S}) \le \frac{\epsilon}{n}\cdot\Psi(\hat{\mathcal S}).$$
--
--   Then $\tilde{\mathcal S}$ is feasible, introduces items only in good periods, and
--
--   $$\Psi(\tilde{\mathcal S}) \ge (1-\epsilon)\cdot\Psi(\hat{\mathcal S}).$$
--
--   This filtering step is what makes the graph $G(\tilde{\mathcal S})$ a collection of uncrossing stars (Lemma 8) while losing only an $\epsilon$-fraction of the profit.
--
--   **Formalization Note.** The paper applies the filter to a maximum-profit good-period solution $\hat{\mathcal S}$; the statement here holds for every feasible good-period solution, since the claim does not use maximality.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 21, §3.3, 'Post-filtering graph properties'

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem filtering (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Shat : Sol I) (hfeas : Feasible I Shat)
    (hgood : ∀ i t, Shat i = some t → IsGood I K ξ t) :
    Feasible I (filt I K (pr I K) Shat) ∧
      (∀ i t, filt I K (pr I K) Shat i = some t → IsGood I K ξ t) ∧
      (1 - eps K) * Psi I (pr I K) Shat ≤ Psi I (pr I K) (filt I K (pr I K) Shat) := by sorry
end IncrKnapsack.PTAS
