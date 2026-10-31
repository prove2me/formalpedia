-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_lemma_9
-- name    : IncrKnapsack.PTAS.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:26.208948+00:00
-- url     : https://prove2.me/theorems/073628ee-0809-44e9-ab22-8e762d506ffa
-- title:
--   Lemma 9, p. 24 — an optimal multi-cluster solution splits into an optimal (m − 1)-cluster solution and an optimal single-cluster solution
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, let $\xi \in \{0,\dots,K-1\}$, and work with the rounded profits of §2.2. Let $\mathcal S$ be an optimal solution of the multi-cluster instance $\mathcal I^{\varphi_m}_{\mathrm{multi}}[m, \ell_m]$: a feasible uncrossing-stars solution that introduces items only in good periods of $\mathcal C_1, \dots, \mathcal C_m$, uses only the classes $\mathcal P_0, \dots, \mathcal P_{\ell_m}$, has profit at least $\varphi_m$, and has weight $w(\mathcal S) = F(m, \ell_m, \varphi_m)$. Decompose $\mathcal S$ into two parts: $\mathcal S^{<m}$, the items introduced in $\mathcal C_1, \dots, \mathcal C_{m-1}$, and $\mathcal S^m$, the items introduced in $\mathcal C_m$. Let $\varphi_{m-1} = \Psi(\mathcal S^{<m})$, and let $\ell_{m-1}$ be the largest class index used by $\mathcal S^{<m}$ ($-1$ if it is empty). Then
--
--   $$F(m-1, \ell_{m-1}, \varphi_{m-1}) = w(\mathcal S^{<m}), \qquad \mathrm{OPT}\Big(\mathcal I^{\varphi_m - \varphi_{m-1},\, w(\mathcal S^{<m})}_{\mathrm{single}}[m, \ell_{m-1}+1, \ell_m]\Big) = w(\mathcal S^m).$$
--
--   That is, $\mathcal S^{<m}$ is optimal for the $(m-1)$-cluster instance and $\mathcal S^m$ is optimal for the single-cluster instance. This optimal substructure yields the recursion for $F$ (equation (6) and the display after it on p. 25).
--
--   **Formalization Note.** Lean indexes the clusters as `m + 1` and `m`, and the class bounds are shifted: the hypothesis uses `j + 1` for $\ell_m + 1$, and `classTop` of $\mathcal S^{<m}$ is $\ell_{m-1}+1$. The single-cluster profit is the sum of item contributions with the full-horizon $\lambda^{t+}$. Page 23 instead writes $\sum_{t \in \mathcal C_m}\lambda_t p(S_t)$, under which the additivity $\Psi(\mathcal S) = \Psi(\mathcal S^{<m}) + \Psi(\mathcal S^m)$ used in the proof fails.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 23–24, §3.4, Lemma 9

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem lemma_9 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (m j : ℕ) (ϕ : ℝ) (S : Sol I) (hS : MultiFeas I K ξ (m + 1) (j + 1) ϕ S)
    (hSopt : ((weight I S : ℝ) : WithTop ℝ) = F I K ξ (m + 1) (j + 1) ϕ) :
    F I K ξ m (classTop I K (lowPart I K ξ S m)) (contrib I (pr I K) (lowPart I K ξ S m)) =
        ((weight I (lowPart I K ξ S m) : ℝ) : WithTop ℝ) ∧
      OPTsingle I K ξ (m + 1) (classTop I K (lowPart I K ξ S m)) j
          (ϕ - contrib I (pr I K) (lowPart I K ξ S m)) (weight I (lowPart I K ξ S m)) =
        ((weight I (highPart I K ξ S m) : ℝ) : WithTop ℝ) := by sorry
end IncrKnapsack.PTAS
