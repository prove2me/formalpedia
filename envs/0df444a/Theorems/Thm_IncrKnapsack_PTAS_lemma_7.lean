-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_lemma_7
-- name    : IncrKnapsack.PTAS.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:17.124412+00:00
-- url     : https://prove2.me/theorems/a4d68a3a-2bdc-47ff-a908-d94b2c3a9135
-- title:
--   Lemma 7, p. 21 — averaged over the shift ξ, dropping bad-interval introductions keeps a (1 − ε) fraction of Ψ
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, and let $\epsilon = 1/K$ with $K > 4$ an integer. The time periods are partitioned into the intervals $I_1, I_2, \dots$ of §3.2, where $I_m$ collects the periods with $\lambda^{t+} \in ((\epsilon/n)^m\lambda^{1+}, (\epsilon/n)^{m-1}\lambda^{1+}]$. For a shift $\xi \in \{0, \dots, K-1\}$, call $I_m$ bad when $m \bmod K = \xi$. Given a solution $\mathcal S$ and any profit vector, let $\mathcal S_\xi$ be obtained from $\mathcal S$ by deleting every item introduced in a period of a bad interval. Then, with $\xi$ uniform on $\{0, \dots, K-1\}$,
--
--   $$\mathbb E_\xi\big[\Psi(\mathcal S_\xi)\big] = \frac1K\sum_{\xi=0}^{K-1}\Psi(\mathcal S_\xi) = (1-\epsilon)\cdot\Psi(\mathcal S).$$
--
--   Consequently some shift $\xi$ satisfies $\Psi(\mathcal S_\xi) \ge (1-\epsilon)\Psi(\mathcal S)$. Section 3.3 fixes such a shift for an optimal $\mathcal S = \mathcal S^*$.
--
--   **Formalization Note.** The paper states the lemma for an optimal solution $\mathcal S^*$; its proof never uses optimality, and the statement here holds for every solution and every profit vector. The expectation is written as the average over the $K$ shifts.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 20–21, §3.2, Lemma 7

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem lemma_7 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K)
    (p : Fin I.n → ℝ) (S : Sol I) :
    (1 / (K : ℝ)) * ∑ ξ ∈ range K, Psi I p (restrictGood I K ξ S) = (1 - eps K) * Psi I p S := by sorry
end IncrKnapsack.PTAS
