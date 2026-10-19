-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_binomial_le_finrank_of_eigenvector_mem
-- name    : OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:27:41.971447+00:00
-- url     : https://prove2.me/theorems/a796e787-d163-45dc-9632-3bb501d9ce16
-- title:
--   Binomial lower bound for the dimension of a permutation-stable subspace containing a sign eigenvector
-- statement:
--   Let $\iota$ be a finite set with $n=|\iota|$ elements and let $V$ be a finite-dimensional real vector space. Let $(A_i)_{i\in\iota}$ be pairwise commuting linear maps $V\to V$. Suppose that for every permutation $p$ of $\iota$ a linear isomorphism $P_p:V\to V$ is given such that $A_{p(i)}P_p=P_pA_i$ for all $i\in\iota$, and let $W\subseteq V$ be a linear subspace with $P_pW\subseteq W$ for every permutation $p$. Let $s\subseteq\iota$ and let $v\in W$ with $v\neq0$ satisfy
--   $$
--   A_iv=-v\quad (i\in s),\qquad A_iv=v\quad (i\notin s).
--   $$
--   Then
--   $$
--   \binom{n}{|s|}\le\dim W .
--   $$
--
--   No further structure is assumed: $p\mapsto P_p$ need not be a group homomorphism, the $A_i$ need not be involutions, and $W$ need not be invariant under the $A_i$. The statement says that a subspace stable under the permuting operators that contains one joint eigenvector with sign pattern $s$ contains a joint eigenvector for every sign pattern of the same size, and these are linearly independent. In the matching argument the $A_i$ are the swaps of the two vertices of the $i$-th standard pair acting on functions of matchings and $P_p$ is the action of relabelling the pairs; the lemma converts a single sign eigenvector in a permutation-invariant space of functions into a binomial lower bound on its dimension.
--
--   **Formalization Note** The operators are `A : ι → Module.End ℝ V` and `P : Equiv.Perm ι → V ≃ₗ[ℝ] V`, the intertwining hypothesis is stated pointwise as `A (p i) (P p v) = P p (A i v)`, $s$ is a `Finset ι`, and $\dim W$ is `Module.finrank ℝ W`. The sign pattern is written `A i v = (if i ∈ s then -1 else 1) • v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Involutions.lean#L155-L188

import Mathlib
import Definitions.Def_MatchingPSD

open OAI
universe u_1 u_2 u_3
variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

theorem OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (P : Equiv.Perm ι → V ≃ₗ[ℝ] V)
    (hconj : ∀ p i v, A (p i) (P p v) = P p (A i v))
    (W : Submodule ℝ V) (hW : ∀ p v, v ∈ W → P p v ∈ W)
    (s : Finset ι) (v : V) (hvW : v ∈ W) (hv : v ≠ 0)
    (heig : ∀ i, A i v = (if i ∈ s then (-1 : ℝ) else 1) • v) :
    (Fintype.card ι).choose s.card ≤ Module.finrank ℝ W := by sorry
