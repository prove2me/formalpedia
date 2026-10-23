-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_lemma_8
-- name    : IncrKnapsack.PTAS.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:15.893858+00:00
-- url     : https://prove2.me/theorems/ebc45474-dd7b-4d95-a262-8f9434a662da
-- title:
--   Lemma 8, p. 22 — after filtering, the cluster–profit-class graph G(S̃) is a collection of uncrossing stars
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, and let $\xi \in \{0, \dots, K-1\}$. Work with the rounded profits of §2.2, so that every item of class $\mathcal P_\ell$ has profit $(1+\epsilon)^\ell$. Let $\hat{\mathcal S}$ be a solution that introduces items only in periods of good intervals. Let $\tilde{\mathcal S}$ be obtained from it by eliminating every item with $\Psi_i(\hat{\mathcal S}) \le (\epsilon/n)\Psi(\hat{\mathcal S})$. In the bipartite graph $G(\tilde{\mathcal S})$ there is an edge $(\mathcal C_m, \mathcal P_\ell)$ when some item of $\mathcal P_\ell$ is introduced by $\tilde{\mathcal S}$ in a period of $\mathcal C_m$. Then $G(\tilde{\mathcal S})$ is a collection of uncrossing stars:
--
--   1. ($\mathcal P$-degrees) every vertex $\mathcal P_\ell$ has degree at most $1$;
--   2. (uncrossing) there are no edges $(\mathcal C_{m_1}, \mathcal P_{\ell_1})$ and $(\mathcal C_{m_2}, \mathcal P_{\ell_2})$ with $\ell_1 < \ell_2$ and $m_1 > m_2$.
--
--   Hence a near-optimal solution decomposes into stars centred at clusters, with the profit classes increasing from cluster to cluster. The dynamic programs of §3.4–§3.5 search over exactly this structure.
--
--   **Formalization Note.** The paper proves property 1 and says property 2 follows "via nearly identical arguments"; both are stated. The paper's $\hat{\mathcal S}$ is a maximum-profit good-period solution, but the proof uses no maximality, so the statement holds for every good-period solution. In Lean the properties are phrased on introduced items: two items of the same class lie in the same cluster, and an item of a lower class lies in a cluster no later than an item of a higher class.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 21–22, §3.3, Lemma 8

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem lemma_8 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Shat : Sol I) (hgood : ∀ i t, Shat i = some t → IsGood I K ξ t) :
    UncrossingStars I K ξ (filt I K (pr I K) Shat) := by sorry
end IncrKnapsack.PTAS
