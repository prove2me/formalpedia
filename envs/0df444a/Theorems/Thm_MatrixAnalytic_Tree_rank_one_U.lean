-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_rank_one_U
-- name    : MatrixAnalytic.Tree.rank_one_U
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:08.21933+00:00
-- url     : https://prove2.me/theorems/29ca4588-4dd0-4393-90bd-62c2e516eac5
-- title:
--   Lemma 14.3.6 — D_i = d·δ_i of rank one: U = C + Σ_i A_i1·δ_i if the process is recurrent
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$, and let $U$ be the generator of the process in the local time of the root node $s\{\cdot\}$ before the first passage to $\emptyset$. Assume the matrices $D_i$ are of rank one,
--
--   $$D_i = \boldsymbol d \cdot \boldsymbol\delta_i, \qquad 1 \le i \le m,$$
--
--   where each $\boldsymbol\delta_i$ is a row vector with $\boldsymbol\delta_i\mathbf 1 = 1$. If the process is recurrent, then
--
--   $$U = C + \sum_{1 \le i \le m} A_i\mathbf 1 \cdot \boldsymbol\delta_i .$$
--
--   This applies to M/PH/1 queues under the last-come-first-served discipline, where $D_i = \boldsymbol t \cdot \boldsymbol e_i$; there $U$, hence $R = A(-U)^{-1}$, is explicit and the condition $\mathrm{sp}(R) < 1$ can be checked directly.
--
--   **Formalization Note** Phases form an arbitrary countable type, so the sums over $i$ and the products $A_i\mathbf 1$ are `tsum`s; the rank-one assumption is expressed by the factorization $[D_i]_{kj} = d_k (\boldsymbol\delta_i)_j$ itself, with $\sum_j (\boldsymbol\delta_i)_j = 1$. $U$ is defined probabilistically (rates and first-entry probabilities), not by (14.6).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 293, Lemma 14.3.6

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Lemma 14.3.6, p. 293: assume the matrices `D_i` are of rank one, `D_i = d · δ_i` (14.10),
with `δ_i` a row vector such that `δ_i 1 = 1`. If the process is recurrent, then
`U = C + Σ_i A_i 1 · δ_i`. -/
theorem rank_one_U {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (δ : ι → ι → ℝ) (hδ : ∀ i : ι, HasSum (δ i) 1)
    (hD : ∀ i k j : ι, T.D i k j = T.d k * δ i j)
    (hrec : IsRecurrentProcess (gen T)) :
    ∀ k j : ι, matU T k j = T.C k j + ∑' i : ι, (∑' i' : ι, T.A i k i') * δ i j := by sorry

end MatrixAnalytic.Tree
